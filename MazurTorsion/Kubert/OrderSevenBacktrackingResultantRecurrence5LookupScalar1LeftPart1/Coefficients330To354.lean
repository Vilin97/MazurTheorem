/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupLeadingSquare
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupA1
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupScalar1LeftPart1Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 5 lookup certificate: Scalar1Left coefficient convolution

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence5LeadingSquare_coeff_0
  recurrence5LeadingSquare_coeff_1
  recurrence5LeadingSquare_coeff_2
  recurrence5LeadingSquare_coeff_3
  recurrence5LeadingSquare_coeff_4
  recurrence5LeadingSquare_coeff_5
  recurrence5LeadingSquare_coeff_6
  recurrence5LeadingSquare_coeff_7
  recurrence5LeadingSquare_coeff_8
  recurrence5LeadingSquare_coeff_9
  recurrence5LeadingSquare_coeff_10
  recurrence5LeadingSquare_coeff_11
  recurrence5LeadingSquare_coeff_12
  recurrence5LeadingSquare_coeff_13
  recurrence5LeadingSquare_coeff_14
  recurrence5LeadingSquare_coeff_15
  recurrence5LeadingSquare_coeff_16
  recurrence5LeadingSquare_coeff_17
  recurrence5LeadingSquare_coeff_18
  recurrence5LeadingSquare_coeff_19
  recurrence5LeadingSquare_coeff_20
  recurrence5LeadingSquare_coeff_21
  recurrence5LeadingSquare_coeff_22
  recurrence5LeadingSquare_coeff_23
  recurrence5LeadingSquare_coeff_24
  recurrence5LeadingSquare_coeff_25
  recurrence5LeadingSquare_coeff_26
  recurrence5LeadingSquare_coeff_27
  recurrence5LeadingSquare_coeff_28
  recurrence5LeadingSquare_coeff_29
  recurrence5LeadingSquare_coeff_30
  recurrence5LeadingSquare_coeff_31
  recurrence5LeadingSquare_coeff_32
  recurrence5LeadingSquare_coeff_33
  recurrence5LeadingSquare_coeff_34
  recurrence5LeadingSquare_coeff_35
  recurrence5LeadingSquare_coeff_36
  recurrence5LeadingSquare_coeff_37
  recurrence5LeadingSquare_coeff_38
  recurrence5LeadingSquare_coeff_39
  recurrence5LeadingSquare_coeff_40
  recurrence5LeadingSquare_coeff_41
  recurrence5LeadingSquare_coeff_42
  recurrence5LeadingSquare_coeff_43
  recurrence5LeadingSquare_coeff_44
  recurrence5LeadingSquare_coeff_45
  recurrence5LeadingSquare_coeff_46
  recurrence5LeadingSquare_coeff_47
  recurrence5LeadingSquare_coeff_48
  recurrence5LeadingSquare_coeff_49
  recurrence5LeadingSquare_coeff_50
  recurrence5LeadingSquare_coeff_51
  recurrence5LeadingSquare_coeff_52
  recurrence5LeadingSquare_coeff_53
  recurrence5LeadingSquare_coeff_54
  recurrence5LeadingSquare_coeff_55
  recurrence5LeadingSquare_coeff_56
  recurrence5LeadingSquare_coeff_57
  recurrence5LeadingSquare_coeff_58
  recurrence5LeadingSquare_coeff_59
  recurrence5LeadingSquare_coeff_60
  recurrence5LeadingSquare_coeff_61
  recurrence5LeadingSquare_coeff_62
  recurrence5LeadingSquare_coeff_63

attribute [local simp]
  recurrence5LeadingSquare_coeff_64
  recurrence5LeadingSquare_coeff_65
  recurrence5LeadingSquare_coeff_66
  recurrence5LeadingSquare_coeff_67
  recurrence5LeadingSquare_coeff_68
  recurrence5LeadingSquare_coeff_69
  recurrence5LeadingSquare_coeff_70
  recurrence5LeadingSquare_coeff_71
  recurrence5LeadingSquare_coeff_72
  recurrence5LeadingSquare_coeff_73
  recurrence5LeadingSquare_coeff_74
  recurrence5LeadingSquare_coeff_75
  recurrence5LeadingSquare_coeff_76
  recurrence5LeadingSquare_coeff_77
  recurrence5LeadingSquare_coeff_78
  recurrence5LeadingSquare_coeff_79
  recurrence5LeadingSquare_coeff_80
  recurrence5LeadingSquare_coeff_81
  recurrence5LeadingSquare_coeff_82
  recurrence5LeadingSquare_coeff_83
  recurrence5LeadingSquare_coeff_84
  recurrence5LeadingSquare_coeff_85
  recurrence5LeadingSquare_coeff_86
  recurrence5LeadingSquare_coeff_87
  recurrence5LeadingSquare_coeff_88
  recurrence5LeadingSquare_coeff_89
  recurrence5LeadingSquare_coeff_90
  recurrence5LeadingSquare_coeff_91
  recurrence5LeadingSquare_coeff_92
  recurrence5LeadingSquare_coeff_93
  recurrence5LeadingSquare_coeff_94
  recurrence5LeadingSquare_coeff_95
  recurrence5LeadingSquare_coeff_96
  recurrence5LeadingSquare_coeff_97
  recurrence5LeadingSquare_coeff_98
  recurrence5LeadingSquare_coeff_99
  recurrence5LeadingSquare_coeff_100
  recurrence5LeadingSquare_coeff_101
  recurrence5LeadingSquare_coeff_102
  recurrence5LeadingSquare_coeff_103
  recurrence5LeadingSquare_coeff_104
  recurrence5LeadingSquare_coeff_105
  recurrence5LeadingSquare_coeff_106
  recurrence5LeadingSquare_coeff_107
  recurrence5LeadingSquare_coeff_108
  recurrence5LeadingSquare_coeff_109
  recurrence5LeadingSquare_coeff_110
  recurrence5LeadingSquare_coeff_111
  recurrence5LeadingSquare_coeff_112
  recurrence5LeadingSquare_coeff_113
  recurrence5LeadingSquare_coeff_114
  recurrence5LeadingSquare_coeff_115
  recurrence5LeadingSquare_coeff_116
  recurrence5LeadingSquare_coeff_117
  recurrence5LeadingSquare_coeff_118
  recurrence5LeadingSquare_coeff_119
  recurrence5LeadingSquare_coeff_120
  recurrence5LeadingSquare_coeff_121
  recurrence5LeadingSquare_coeff_122
  recurrence5LeadingSquare_coeff_123
  recurrence5LeadingSquare_coeff_124
  recurrence5LeadingSquare_coeff_125
  recurrence5LeadingSquare_coeff_126
  recurrence5LeadingSquare_coeff_127

attribute [local simp]
  recurrence5LeadingSquare_coeff_128
  recurrence5LeadingSquare_coeff_129
  recurrence5LeadingSquare_coeff_130
  recurrence5LeadingSquare_coeff_131
  recurrence5LeadingSquare_coeff_132
  recurrence5LeadingSquare_coeff_133
  recurrence5LeadingSquare_coeff_134
  recurrence5LeadingSquare_coeff_135
  recurrence5LeadingSquare_coeff_136
  recurrence5LeadingSquare_coeff_137
  recurrence5LeadingSquare_coeff_138
  recurrence5LeadingSquare_coeff_139
  recurrence5LeadingSquare_coeff_140
  recurrence5LeadingSquare_coeff_141
  recurrence5LeadingSquare_coeff_142
  recurrence5LeadingSquare_coeff_143
  recurrence5LeadingSquare_coeff_144
  recurrence5LeadingSquare_coeff_145
  recurrence5LeadingSquare_coeff_146
  recurrence5LeadingSquare_coeff_147
  recurrence5LeadingSquare_coeff_148
  recurrence5LeadingSquare_coeff_149
  recurrence5LeadingSquare_coeff_150
  recurrence5LeadingSquare_coeff_151
  recurrence5LeadingSquare_coeff_152
  recurrence5LeadingSquare_coeff_153
  recurrence5LeadingSquare_coeff_154
  recurrence5LeadingSquare_coeff_155
  recurrence5LeadingSquare_coeff_156
  recurrence5LeadingSquare_coeff_157
  recurrence5LeadingSquare_coeff_158
  recurrence5LeadingSquare_coeff_159
  recurrence5LeadingSquare_coeff_160
  recurrence5LeadingSquare_coeff_161
  recurrence5LeadingSquare_coeff_162
  recurrence5LeadingSquare_coeff_163
  recurrence5LeadingSquare_coeff_164
  recurrence5LeadingSquare_coeff_165
  recurrence5LeadingSquare_coeff_166
  recurrence5LeadingSquare_coeff_167
  recurrence5LeadingSquare_coeff_168
  recurrence5LeadingSquare_coeff_169
  recurrence5LeadingSquare_coeff_170
  recurrence5LeadingSquare_coeff_171
  recurrence5LeadingSquare_coeff_172
  recurrence5LeadingSquare_coeff_173
  recurrence5LeadingSquare_coeff_174
  recurrence5LeadingSquare_coeff_175
  recurrence5LeadingSquare_coeff_176
  recurrence5LeadingSquare_coeff_177
  recurrence5LeadingSquare_coeff_178
  recurrence5LeadingSquare_coeff_179
  recurrence5LeadingSquare_coeff_180
  recurrence5LeadingSquare_coeff_181
  recurrence5LeadingSquare_coeff_182
  recurrence5LeadingSquare_coeff_183
  recurrence5LeadingSquare_coeff_184
  recurrence5LeadingSquare_coeff_185
  recurrence5LeadingSquare_coeff_186
  recurrence5LeadingSquare_coeff_187
  recurrence5LeadingSquare_coeff_188
  recurrence5LeadingSquare_coeff_189
  recurrence5LeadingSquare_coeff_190
  recurrence5LeadingSquare_coeff_191

attribute [local simp]
  recurrence5LeadingSquare_coeff_192
  recurrence5LeadingSquare_coeff_193
  recurrence5LeadingSquare_coeff_194
  recurrence5LeadingSquare_coeff_195
  recurrence5LeadingSquare_coeff_196
  recurrence5LeadingSquare_coeff_197
  recurrence5LeadingSquare_coeff_198
  recurrence5LeadingSquare_coeff_199
  recurrence5LeadingSquare_coeff_200
  recurrence5LeadingSquare_coeff_201
  recurrence5LeadingSquare_coeff_202
  recurrence5LeadingSquare_coeff_203
  recurrence5LeadingSquare_coeff_204
  recurrence5LeadingSquare_coeff_205
  recurrence5LeadingSquare_coeff_206
  recurrence5LeadingSquare_coeff_207
  recurrence5LeadingSquare_coeff_208
  recurrence5LeadingSquare_coeff_209
  recurrence5LeadingSquare_coeff_210
  recurrence5LeadingSquare_coeff_211
  recurrence5LeadingSquare_coeff_212
  recurrence5LeadingSquare_coeff_213
  recurrence5LeadingSquare_coeff_214
  recurrence5LeadingSquare_coeff_215
  recurrence5LeadingSquare_coeff_216
  recurrence5LeadingSquare_coeff_217
  recurrence5LeadingSquare_coeff_218
  recurrence5LeadingSquare_coeff_219
  recurrence5LeadingSquare_coeff_220
  recurrence5LeadingSquare_coeff_221
  recurrence5LeadingSquare_coeff_222
  recurrence5LeadingSquare_coeff_223
  recurrence5LeadingSquare_coeff_224
  recurrence5LeadingSquare_coeff_225
  recurrence5LeadingSquare_coeff_226
  recurrence5LeadingSquare_coeff_227
  recurrence5LeadingSquare_coeff_228
  recurrence5LeadingSquare_coeff_229
  recurrence5LeadingSquare_coeff_230
  recurrence5LeadingSquare_coeff_231
  recurrence5LeadingSquare_coeff_232
  recurrence5LeadingSquare_coeff_233
  recurrence5LeadingSquare_coeff_234
  recurrence5LeadingSquare_coeff_235
  recurrence5LeadingSquare_coeff_236
  recurrence5LeadingSquare_coeff_237
  recurrence5LeadingSquare_coeff_238
  recurrence5LeadingSquare_coeff_239
  recurrence5LeadingSquare_coeff_240
  recurrence5LeadingSquare_coeff_241
  recurrence5LeadingSquare_coeff_242
  recurrence5LeadingSquare_coeff_243
  recurrence5LeadingSquare_coeff_244
  recurrence5LeadingSquare_coeff_245
  recurrence5LeadingSquare_coeff_246
  recurrence5LeadingSquare_coeff_247
  recurrence5LeadingSquare_coeff_248
  recurrence5LeadingSquare_coeff_249
  recurrence5LeadingSquare_coeff_250
  recurrence5LeadingSquare_coeff_251
  recurrence5LeadingSquare_coeff_252
  recurrence5LeadingSquare_coeff_253
  recurrence5LeadingSquare_coeff_254
  recurrence5LeadingSquare_coeff_255

attribute [local simp]
  recurrence5LeadingSquare_coeff_256
  recurrence5LeadingSquare_coeff_257
  recurrence5LeadingSquare_coeff_258
  recurrence5LeadingSquare_coeff_259
  recurrence5LeadingSquare_coeff_260
  recurrence5LeadingSquare_coeff_261
  recurrence5LeadingSquare_coeff_262
  recurrence5LeadingSquare_coeff_263
  recurrence5LeadingSquare_coeff_264
  recurrence5LeadingSquare_coeff_265
  recurrence5LeadingSquare_coeff_266
  recurrence5LeadingSquare_coeff_267
  recurrence5LeadingSquare_coeff_268
  recurrence5LeadingSquare_coeff_269
  recurrence5LeadingSquare_coeff_270
  recurrence5LeadingSquare_coeff_271
  recurrence5LeadingSquare_coeff_272
  recurrence5LeadingSquare_coeff_273
  recurrence5LeadingSquare_coeff_274
  recurrence5LeadingSquare_coeff_275
  recurrence5LeadingSquare_coeff_276
  recurrence5LeadingSquare_coeff_277
  recurrence5LeadingSquare_coeff_278
  recurrence5LeadingSquare_coeff_279
  recurrence5LeadingSquare_coeff_280
  recurrence5LeadingSquare_coeff_281
  recurrence5LeadingSquare_coeff_282
  recurrence5LeadingSquare_coeff_283
  recurrence5LeadingSquare_coeff_284
  recurrence5LeadingSquare_coeff_285
  recurrence5LeadingSquare_coeff_286
  recurrence5LeadingSquare_coeff_287
  recurrence5LeadingSquare_coeff_288
  recurrence5LeadingSquare_coeff_289
  recurrence5LeadingSquare_coeff_290
  recurrence5A1_coeff_0
  recurrence5A1_coeff_1
  recurrence5A1_coeff_2
  recurrence5A1_coeff_3
  recurrence5A1_coeff_4
  recurrence5A1_coeff_5
  recurrence5A1_coeff_6
  recurrence5A1_coeff_7
  recurrence5A1_coeff_8
  recurrence5A1_coeff_9
  recurrence5A1_coeff_10
  recurrence5A1_coeff_11
  recurrence5A1_coeff_12
  recurrence5A1_coeff_13
  recurrence5A1_coeff_14
  recurrence5A1_coeff_15
  recurrence5A1_coeff_16
  recurrence5A1_coeff_17
  recurrence5A1_coeff_18
  recurrence5A1_coeff_19
  recurrence5A1_coeff_20
  recurrence5A1_coeff_21
  recurrence5A1_coeff_22
  recurrence5A1_coeff_23
  recurrence5A1_coeff_24
  recurrence5A1_coeff_25
  recurrence5A1_coeff_26
  recurrence5A1_coeff_27
  recurrence5A1_coeff_28

attribute [local simp]
  recurrence5A1_coeff_29
  recurrence5A1_coeff_30
  recurrence5A1_coeff_31
  recurrence5A1_coeff_32
  recurrence5A1_coeff_33
  recurrence5A1_coeff_34
  recurrence5A1_coeff_35
  recurrence5A1_coeff_36
  recurrence5A1_coeff_37
  recurrence5A1_coeff_38
  recurrence5A1_coeff_39
  recurrence5A1_coeff_40
  recurrence5A1_coeff_41
  recurrence5A1_coeff_42
  recurrence5A1_coeff_43
  recurrence5A1_coeff_44
  recurrence5A1_coeff_45
  recurrence5A1_coeff_46
  recurrence5A1_coeff_47
  recurrence5A1_coeff_48
  recurrence5A1_coeff_49
  recurrence5A1_coeff_50
  recurrence5A1_coeff_51
  recurrence5A1_coeff_52
  recurrence5A1_coeff_53
  recurrence5A1_coeff_54
  recurrence5A1_coeff_55
  recurrence5A1_coeff_56
  recurrence5A1_coeff_57
  recurrence5A1_coeff_58
  recurrence5A1_coeff_59
  recurrence5A1_coeff_60
  recurrence5A1_coeff_61
  recurrence5A1_coeff_62
  recurrence5A1_coeff_63
  recurrence5A1_coeff_64
  recurrence5A1_coeff_65
  recurrence5A1_coeff_66
  recurrence5A1_coeff_67
  recurrence5A1_coeff_68
  recurrence5A1_coeff_69
  recurrence5A1_coeff_70
  recurrence5A1_coeff_71
  recurrence5A1_coeff_72
  recurrence5A1_coeff_73
  recurrence5A1_coeff_74
  recurrence5A1_coeff_75
  recurrence5A1_coeff_76
  recurrence5A1_coeff_77
  recurrence5A1_coeff_78
  recurrence5A1_coeff_79
  recurrence5A1_coeff_80
  recurrence5A1_coeff_81
  recurrence5A1_coeff_82
  recurrence5A1_coeff_83
  recurrence5A1_coeff_84
  recurrence5A1_coeff_85
  recurrence5A1_coeff_86
  recurrence5A1_coeff_87
  recurrence5A1_coeff_88
  recurrence5A1_coeff_89
  recurrence5A1_coeff_90
  recurrence5A1_coeff_91
  recurrence5A1_coeff_92

attribute [local simp]
  recurrence5A1_coeff_93
  recurrence5A1_coeff_94
  recurrence5A1_coeff_95
  recurrence5A1_coeff_96
  recurrence5A1_coeff_97
  recurrence5A1_coeff_98
  recurrence5A1_coeff_99
  recurrence5A1_coeff_100
  recurrence5A1_coeff_101
  recurrence5A1_coeff_102
  recurrence5A1_coeff_103
  recurrence5A1_coeff_104
  recurrence5A1_coeff_105
  recurrence5A1_coeff_106
  recurrence5A1_coeff_107
  recurrence5A1_coeff_108
  recurrence5A1_coeff_109
  recurrence5A1_coeff_110
  recurrence5A1_coeff_111
  recurrence5A1_coeff_112
  recurrence5A1_coeff_113
  recurrence5A1_coeff_114
  recurrence5A1_coeff_115
  recurrence5A1_coeff_116
  recurrence5A1_coeff_117
  recurrence5A1_coeff_118
  recurrence5A1_coeff_119
  recurrence5A1_coeff_120
  recurrence5A1_coeff_121
  recurrence5A1_coeff_122
  recurrence5A1_coeff_123
  recurrence5A1_coeff_124
  recurrence5A1_coeff_125
  recurrence5A1_coeff_126
  recurrence5A1_coeff_127
  recurrence5A1_coeff_128
  recurrence5A1_coeff_129
  recurrence5A1_coeff_130
  recurrence5A1_coeff_131
  recurrence5A1_coeff_132
  recurrence5A1_coeff_133
  recurrence5A1_coeff_134
  recurrence5A1_coeff_135
  recurrence5A1_coeff_136
  recurrence5A1_coeff_137
  recurrence5A1_coeff_138
  recurrence5A1_coeff_139
  recurrence5A1_coeff_140
  recurrence5A1_coeff_141
  recurrence5A1_coeff_142
  recurrence5A1_coeff_143
  recurrence5A1_coeff_144
  recurrence5A1_coeff_145
  recurrence5A1_coeff_146
  recurrence5A1_coeff_147
  recurrence5A1_coeff_148
  recurrence5A1_coeff_149
  recurrence5A1_coeff_150
  recurrence5A1_coeff_151
  recurrence5A1_coeff_152
  recurrence5A1_coeff_153
  recurrence5A1_coeff_154
  recurrence5A1_coeff_155
  recurrence5A1_coeff_156

attribute [local simp]
  recurrence5A1_coeff_157
  recurrence5A1_coeff_158
  recurrence5A1_coeff_159
  recurrence5A1_coeff_160
  recurrence5A1_coeff_161
  recurrence5A1_coeff_162
  recurrence5A1_coeff_163
  recurrence5A1_coeff_164
  recurrence5A1_coeff_165
  recurrence5A1_coeff_166
  recurrence5A1_coeff_167
  recurrence5A1_coeff_168
  recurrence5A1_coeff_169
  recurrence5A1_coeff_170
  recurrence5A1_coeff_171
  recurrence5A1_coeff_172

private theorem recurrence5Scalar1Left_coeff_330_prefix_zero :
    (∑ x ∈ Finset.range 158,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (330 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (330 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_330_suffix_zero :
    (∑ x ∈ Finset.range 40,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (330 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_330 :
    recurrence5Scalar1Left.coeff 330 =
      -(((((56051042166687056285687315162047163035340301877110380 * 10 ^ 70 +
        9272055852460843615725200357028970010918792166839058674089044712164994) * 10 ^ 70 +
        3164587956893685045038928265698255398024477058322555186136984428593691) * 10 ^ 70 +
        9554418778494425640600871222339808002836108674314854184731195467380573) * 10 ^ 70 +
        7434066611824953647553591308970998437405332559884244714792125221342187) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 331 = 158 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 77 = 32 +
      45 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 45 = 5 +
      40 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_330_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_330_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_331_prefix_zero :
    (∑ x ∈ Finset.range 159,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (331 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (331 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_331_suffix_zero :
    (∑ x ∈ Finset.range 41,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (331 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_331 :
    recurrence5Scalar1Left.coeff 331 =
      (((((23807168861878316919733451421413877426623473203418188 * 10 ^ 70 +
        8161387135282051933596320130249253996231111742725991509179899655447776) * 10 ^ 70 +
        7163667057861265490232435158426059813544367810442080284308827336803266) * 10 ^ 70 +
        8782743124431253861773566471367533053114750405817206609387665189748172) * 10 ^ 70 +
        1924102683404471220815225626074312272003124107302804521638556370023467) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 332 = 159 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 77 = 32 +
      45 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 45 = 4 +
      41 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_331_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_331_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_332_prefix_zero :
    (∑ x ∈ Finset.range 160,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (332 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (332 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_332_suffix_zero :
    (∑ x ∈ Finset.range 42,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (332 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_332 :
    recurrence5Scalar1Left.coeff 332 =
      -(((((9705777982261981065411566692613831950486193476904187 * 10 ^ 70 +
        9919412930911601261565457014965643117926031735807589119215907750635213) * 10 ^ 70 +
        7072902893956132560051599377175976046468440093199805529472011357253932) * 10 ^ 70 +
        1286740661887412639693761421522272588455859810220410127656803486689379) * 10 ^ 70 +
        2280220795215867189817518380633697880412666665084383626473708158579460) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 333 = 160 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 77 = 32 +
      45 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 45 = 3 +
      42 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_332_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_332_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_333_prefix_zero :
    (∑ x ∈ Finset.range 161,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (333 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (333 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_333_suffix_zero :
    (∑ x ∈ Finset.range 43,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (333 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_333 :
    recurrence5Scalar1Left.coeff 333 =
      (((((3797061375299859120041222054540524463718099472225863 * 10 ^ 70 +
        5477160401258079869513356341399513047399093207545652881291787274399635) * 10 ^ 70 +
        9991308457160788468974678133372030274974241553683596158495841934737839) * 10 ^ 70 +
        8217866622855983420823884258537512721120668130227953455784552987361784) * 10 ^ 70 +
        1722426279888172606263110719585196233326774913654157720731190009876242) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 334 = 161 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 77 = 32 +
      45 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 45 = 2 +
      43 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_333_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_333_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_334_prefix_zero :
    (∑ x ∈ Finset.range 162,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (334 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (334 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_334_suffix_zero :
    (∑ x ∈ Finset.range 44,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (334 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_334 :
    recurrence5Scalar1Left.coeff 334 =
      -(((((1422658283438672956598093133209447328737864156577134 * 10 ^ 70 +
        4945413521187945817937183026384938457337933384843117485907219256176783) * 10 ^ 70 +
        6045280997479816629734217670266336768300070340471484681029710667870253) * 10 ^ 70 +
        1798810156304014704305074085831286288022657069050988874092298735004765) * 10 ^ 70 +
        3070388623766006736335465163563595780059044678732651386071183464299504) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 335 = 162 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 77 = 32 +
      45 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 45 = 1 +
      44 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_334_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_334_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_335_prefix_zero :
    (∑ x ∈ Finset.range 163,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (335 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (335 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_335_suffix_zero :
    (∑ x ∈ Finset.range 45,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (335 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_335 :
    recurrence5Scalar1Left.coeff 335 =
      (((((508266515055879505634281233432623683344439206336139 * 10 ^ 70 +
        6555769746169374049382559320640520953931281309156172696815021909807513) * 10 ^ 70 +
        6138977599598003892801688907450057804302142771204592364323525587060427) * 10 ^ 70 +
        5874676603781548158509193698478246341414945855389215862153426925882849) * 10 ^ 70 +
        5918331765678266367803140444756161053888993746015149377555093938762405) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 336 = 163 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 77 = 32 +
      45 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_335_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_335_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_336_prefix_zero :
    (∑ x ∈ Finset.range 164,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (336 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (336 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_336_suffix_zero :
    (∑ x ∈ Finset.range 46,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (336 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_336 :
    recurrence5Scalar1Left.coeff 336 =
      -(((((171727289682605946172516385723995989876365725738263 * 10 ^ 70 +
        4186370116232472057136327483906391074188025481616954610584436088026014) * 10 ^ 70 +
        2837204327556788560700614067962299863117188634797593183694218865342355) * 10 ^ 70 +
        2030629806246953585908908078072271992557142467518531620665949865775512) * 10 ^ 70 +
        6887355646904355535784478201879754844806968010313289155201309163035755) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 337 = 164 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 77 = 31 +
      46 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_336_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_336_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_337_prefix_zero :
    (∑ x ∈ Finset.range 165,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (337 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (337 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_337_suffix_zero :
    (∑ x ∈ Finset.range 47,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (337 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_337 :
    recurrence5Scalar1Left.coeff 337 =
      (((((54021835365896004551396558550165365619885753776635 * 10 ^ 70 +
        3381644752306283102594896160390306912403128688658999412463330416400287) * 10 ^ 70 +
        2505341359205747975605223832530573543946058432356479423707379237750567) * 10 ^ 70 +
        0947704974843759387226548540343752693478978720486099394940533732351560) * 10 ^ 70 +
        7812191008289308569285276405852861301835017222847115459782947460622505) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 338 = 165 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 77 = 30 +
      47 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_337_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_337_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_338_prefix_zero :
    (∑ x ∈ Finset.range 166,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (338 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (338 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_338_suffix_zero :
    (∑ x ∈ Finset.range 48,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (338 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_338 :
    recurrence5Scalar1Left.coeff 338 =
      -(((((15318062749497515880296051945087045313554612406902 * 10 ^ 70 +
        0229937359874411853392357433925259082257487014089035559125568528773825) * 10 ^ 70 +
        2025940873559422132082201685663090547589772280016616761785129668199444) * 10 ^ 70 +
        1305725169210763018752459211097337813217517061528905220252262311771030) * 10 ^ 70 +
        2846604028627006897861122599146606946302678348184582677210976360070006) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 339 = 166 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 77 = 29 +
      48 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_338_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_338_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_339_prefix_zero :
    (∑ x ∈ Finset.range 167,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (339 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (339 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_339_suffix_zero :
    (∑ x ∈ Finset.range 49,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (339 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_339 :
    recurrence5Scalar1Left.coeff 339 =
      (((((3602084855391479680817245786988830234668580721506 * 10 ^ 70 +
        2831984101512272069981902468040504843336785135728702567044945747574288) * 10 ^ 70 +
        2664233638582899827104091643253590742146170858988756003917667626579741) * 10 ^ 70 +
        1451346023798355814277724705661782039185047256741839986074600550419814) * 10 ^ 70 +
        2178929297664385451202356285012845681106926098100286381680250815949353) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 340 = 167 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 77 = 28 +
      49 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_339_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_339_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_340_prefix_zero :
    (∑ x ∈ Finset.range 168,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (340 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (340 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_340_suffix_zero :
    (∑ x ∈ Finset.range 50,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (340 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_340 :
    recurrence5Scalar1Left.coeff 340 =
      -(((((487239053958519321263058698624812509507100364477 * 10 ^ 70 +
        4553197338461046441672976227666788183696397063671645099754974791740087) * 10 ^ 70 +
        2727341538144233377312896557130137504117000513270333381739701426817553) * 10 ^ 70 +
        4129913396583584727785728640804543467513616769516839024176886810137869) * 10 ^ 70 +
        4732192309054864632429172290059055624715304881910887041925174283103767) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 341 = 168 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 77 = 27 +
      50 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_340_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_340_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_341_prefix_zero :
    (∑ x ∈ Finset.range 169,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (341 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (341 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_341_suffix_zero :
    (∑ x ∈ Finset.range 51,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (341 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_341 :
    recurrence5Scalar1Left.coeff 341 =
      -(((((143539628765772295035615051562440439686399861492 * 10 ^ 70 +
        6740821276696404738726478021690720906658357495304910544920777607362739) * 10 ^ 70 +
        0124888523493765625677888870193857000366116689666856716229265480311048) * 10 ^ 70 +
        5052299613224038900546851131878890006708353400934249824177405603346307) * 10 ^ 70 +
        5878227320035032129438480700748465655290963562012488772346088851798273) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 342 = 169 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 77 = 26 +
      51 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_341_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_341_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_342_prefix_zero :
    (∑ x ∈ Finset.range 170,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (342 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (342 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_342_suffix_zero :
    (∑ x ∈ Finset.range 52,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (342 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_342 :
    recurrence5Scalar1Left.coeff 342 =
      (((((169445405836072686516206846771288832402440491679 * 10 ^ 70 +
        6658759322321089996017043631539350278015633217972451828380431567291025) * 10 ^ 70 +
        3672886771874045904232922280267574634718468431395092736143089042071111) * 10 ^ 70 +
        1937182904520441407633868442735681087909350960134716857760820159416145) * 10 ^ 70 +
        8238818376904104139350046550311963214720823704898575747519302926201648) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 343 = 170 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 77 = 25 +
      52 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_342_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_342_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_343_prefix_zero :
    (∑ x ∈ Finset.range 171,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (343 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (343 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_343_suffix_zero :
    (∑ x ∈ Finset.range 53,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (343 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_343 :
    recurrence5Scalar1Left.coeff 343 =
      -(((((101745146969478687689305572233987795882902757219 * 10 ^ 70 +
        0530919142410314772668364628681543092506969038985171150022594076999021) * 10 ^ 70 +
        0080364748327019026977851777669821464006008173849291049746452390640943) * 10 ^ 70 +
        6361449346964858487344399091972418427710051794765330300732337101375561) * 10 ^ 70 +
        8966451890328698076751804375236915300208105553549183847578664766796231) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 344 = 171 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 77 = 24 +
      53 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_343_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_343_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_344_prefix_zero :
    (∑ x ∈ Finset.range 172,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (344 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (344 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_344_suffix_zero :
    (∑ x ∈ Finset.range 54,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (344 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_344 :
    recurrence5Scalar1Left.coeff 344 =
      (((((49737933096900991966443455519723724541866638830 * 10 ^ 70 +
        6009841281782957443269939151372359899163600327307222660310427836541353) * 10 ^ 70 +
        9982735822040937320247686402583696299134920633608005204011774818854343) * 10 ^ 70 +
        0294464319725989322980850884516312945292317290296717662902739565483825) * 10 ^ 70 +
        3234460462549768736964872606085892691447501018260393359493798919834788) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 345 = 172 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 77 = 23 +
      54 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_344_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_344_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_345_prefix_zero :
    (∑ x ∈ Finset.range 173,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (345 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (345 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_345_suffix_zero :
    (∑ x ∈ Finset.range 55,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (345 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_345 :
    recurrence5Scalar1Left.coeff 345 =
      -(((((21754945416741528654371400834565682783227077748 * 10 ^ 70 +
        9347823297953389661999759338437111561946176943724698982566176755685760) * 10 ^ 70 +
        8129597802908389304753843356191321697456694646238569928774790081609811) * 10 ^ 70 +
        6093515182342883242548941844031954153374076460909241523010325197067338) * 10 ^ 70 +
        4014254827712414496397220749077154566883971908432700664078140159007419) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 346 = 173 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 77 = 22 +
      55 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_345_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_345_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_346_prefix_zero :
    (∑ x ∈ Finset.range 174,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (346 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (346 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_346_suffix_zero :
    (∑ x ∈ Finset.range 56,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (346 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_346 :
    recurrence5Scalar1Left.coeff 346 =
      (((((8816712707818304301370757328019138443142197757 * 10 ^ 70 +
        8143658728049539414190764076293039039588503408797991806159553123508989) * 10 ^ 70 +
        1150325416995848866415547400471849196420851814534138533776579744848149) * 10 ^ 70 +
        6650736425305386014631978890748847203075220663458359331336510645159483) * 10 ^ 70 +
        4992854573035344719734735307359099366787533750521936110956366640248723) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 347 = 174 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 77 = 21 +
      56 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_346_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_346_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_347_prefix_zero :
    (∑ x ∈ Finset.range 175,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (347 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (347 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_347_suffix_zero :
    (∑ x ∈ Finset.range 57,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (347 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_347 :
    recurrence5Scalar1Left.coeff 347 =
      -(((((3363926381520901990289622964029017828730794242 * 10 ^ 70 +
        2782271294894384460927610665606924938040187322621083670097576911463505) * 10 ^ 70 +
        8047203940850381566126500024287249646664997682167004349807655517086323) * 10 ^ 70 +
        0824525031156503769184965256528773623716506873704790324508667751749227) * 10 ^ 70 +
        1825048670994794720252645974501708928258302307781527380751016128831390) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 348 = 175 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 77 = 20 +
      57 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_347_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_347_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_348_prefix_zero :
    (∑ x ∈ Finset.range 176,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (348 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (348 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_348_suffix_zero :
    (∑ x ∈ Finset.range 58,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (348 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_348 :
    recurrence5Scalar1Left.coeff 348 =
      (((((1217214341259415334122243276609632858081768080 * 10 ^ 70 +
        4248573087847723889100734715775795567680035753849860366721652656784014) * 10 ^ 70 +
        5898605263270498951939484753207389360570778957680231794638310970740102) * 10 ^ 70 +
        4267063993782360592417169224101936738151343304953570333890617101703537) * 10 ^ 70 +
        6238056053748059154813365807517416334167578597491976326407131611988296) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 349 = 176 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 77 = 19 +
      58 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_348_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_348_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_349_prefix_zero :
    (∑ x ∈ Finset.range 177,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (349 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (349 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_349_suffix_zero :
    (∑ x ∈ Finset.range 59,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (349 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_349 :
    recurrence5Scalar1Left.coeff 349 =
      -(((((418586386227755604834816876247449611519843378 * 10 ^ 70 +
        7638053015271606779835983656293941818127587959356962795215541393585818) * 10 ^ 70 +
        8555772435167382425634397690778023539251541899539864651329725433301539) * 10 ^ 70 +
        1996586875489286941190898951685516550561676651114267919764766667674507) * 10 ^ 70 +
        5182209386073714414423363152711479993591620132067312701776787860653952) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 350 = 177 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 77 = 18 +
      59 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_349_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_349_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_350_prefix_zero :
    (∑ x ∈ Finset.range 178,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (350 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (350 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_350_suffix_zero :
    (∑ x ∈ Finset.range 60,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (350 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_350 :
    recurrence5Scalar1Left.coeff 350 =
      (((((136464076245194247520843356597393352796331462 * 10 ^ 70 +
        2149898232183138674679346503778392833077426202771901883162848497997097) * 10 ^ 70 +
        3849226949661710346142854962993572600728829971951613049615610766934296) * 10 ^ 70 +
        1270398406542205130604936033991916139554521208402011885183036550043104) * 10 ^ 70 +
        9474448229525299517702663346984628733813397015214227227226174403767077) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 351 = 178 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 77 = 17 +
      60 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_350_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_350_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_351_prefix_zero :
    (∑ x ∈ Finset.range 179,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (351 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (351 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_351_suffix_zero :
    (∑ x ∈ Finset.range 61,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (351 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_351 :
    recurrence5Scalar1Left.coeff 351 =
      -(((((41819943104734012584611079948851021050216720 * 10 ^ 70 +
        6696695957832030954614952280569444324544016701133179785397847983052052) * 10 ^ 70 +
        3962016966487053700723530246568047759379785499385735601676132045381297) * 10 ^ 70 +
        9665268679020308702083869376372257701754016869141588065366342240735828) * 10 ^ 70 +
        8617315637935558314528084379445978578426287871808405866564104516669041) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 352 = 179 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  rw [recurrence5Scalar1Left_coeff_351_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_351_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_352_prefix_zero :
    (∑ x ∈ Finset.range 180,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (352 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (352 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_352_suffix_zero :
    (∑ x ∈ Finset.range 62,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (352 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_352 :
    recurrence5Scalar1Left.coeff 352 =
      (((((11815900975788209829339140280872122666828540 * 10 ^ 70 +
        1320359450019770092829244272666932323263498068087158556627877958271553) * 10 ^ 70 +
        4526617065085973029646124878087857832109837873528844258549158589549307) * 10 ^ 70 +
        9212106094928051764229234171817970071938119399416333193064923385396191) * 10 ^ 70 +
        8058268832841861964288337032715359476584510993945821305286191005885915) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 353 = 180 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 77 = 15 +
      62 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_352_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_352_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_353_prefix_zero :
    (∑ x ∈ Finset.range 181,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (353 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (353 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_353_suffix_zero :
    (∑ x ∈ Finset.range 63,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (353 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_353 :
    recurrence5Scalar1Left.coeff 353 =
      -(((((2939471649259645335018585066053489640303253 * 10 ^ 70 +
        4625532609633233457264416979463995242219867051361518537167813455785149) * 10 ^ 70 +
        2473172897388521506573399574185055673029856175264206032345450735953920) * 10 ^ 70 +
        7065213694485711019933652611711559864155656984884675728816042826413338) * 10 ^ 70 +
        9117241169568434718873822821309704930436723623538500628653475035908594) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 354 = 181 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 77 = 14 +
      63 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_353_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_353_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_354_prefix_zero :
    (∑ x ∈ Finset.range 182,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (354 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (354 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_354_suffix_zero :
    (∑ x ∈ Finset.range 64,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (354 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_354 :
    recurrence5Scalar1Left.coeff 354 =
      (((((557751308408222696520046885866798155466656 * 10 ^ 70 +
        7512589024807818665347405599088745461893605668335859442665582907030322) * 10 ^ 70 +
        0914146052564203903459809744335093490537664060377297753548264172017821) * 10 ^ 70 +
        4554807184190557207354833247386634156285327059641746319948717161018500) * 10 ^ 70 +
        0326579952038742613587186927642816775436232922854483260902757578870267) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 355 = 182 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 77 = 13 +
      64 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_354_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_354_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
