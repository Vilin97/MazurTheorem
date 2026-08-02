/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupLeadingSquare
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupA1
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 5 lookup certificate: Scalar1Left coefficient convolution

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/

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

private theorem recurrence5Scalar1Left_coeff_355_prefix_zero :
    (∑ x ∈ Finset.range 183,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (355 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (355 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_355_suffix_zero :
    (∑ x ∈ Finset.range 65,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (355 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_355 :
    recurrence5Scalar1Left.coeff 355 =
      -(((((19625448485087752675496445326018441060461 * 10 ^ 70 +
        4360371413632368237179498365108621680102666503114354058594886551547333) * 10 ^ 70 +
        3628377469695832421276579106125837316633802334000576201257225966046432) * 10 ^ 70 +
        4548223538467018235434573352619483096333821484985088451635976736587379) * 10 ^ 70 +
        1666922827038435605412577704537002211996726062935528221571196509518666) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 356 = 183 +
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
    rw [show 77 = 12 +
      65 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_355_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_355_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_356_prefix_zero :
    (∑ x ∈ Finset.range 184,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (356 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (356 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_356_suffix_zero :
    (∑ x ∈ Finset.range 66,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (356 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_356 :
    recurrence5Scalar1Left.coeff 356 =
      -(((((55721128449619285483097375280282283018676 * 10 ^ 70 +
        7813799113495905714616495616154688339521698102827557264154953966275481) * 10 ^ 70 +
        9883066543593905334712652976625599904598026320509100733369008904726990) * 10 ^ 70 +
        8323774557924892719384916060351071119138502741755398579038904397574003) * 10 ^ 70 +
        9300057399090049875709860475732960417890913994104552895199784498257470) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 357 = 184 +
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
    rw [show 77 = 11 +
      66 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_356_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_356_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_357_prefix_zero :
    (∑ x ∈ Finset.range 185,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (357 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (357 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_357_suffix_zero :
    (∑ x ∈ Finset.range 67,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (357 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_357 :
    recurrence5Scalar1Left.coeff 357 =
      (((((40973348836364710425008302289579265915408 * 10 ^ 70 +
        6327578541342038888303980280854230588361554588818073780140454534145782) * 10 ^ 70 +
        7189778409517150933766822288527420726389013344500841485016374341373819) * 10 ^ 70 +
        1826985201864394428420284347395445348449343760570679852392728610580044) * 10 ^ 70 +
        9687884225667089391568227867371479065302310334468145446216675428535441) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 358 = 185 +
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
    rw [show 77 = 10 +
      67 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_357_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_357_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_358_prefix_zero :
    (∑ x ∈ Finset.range 186,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (358 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (358 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_358_suffix_zero :
    (∑ x ∈ Finset.range 68,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (358 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_358 :
    recurrence5Scalar1Left.coeff 358 =
      -(((((21456929907710595702837526713300493394312 * 10 ^ 70 +
        8058229631339612008300028443169726762200764314432716545138086888448138) * 10 ^ 70 +
        5755192036656421188314272862860037370255991263549464949080589194477843) * 10 ^ 70 +
        3445880408973903312338802239084224457483885512325162717199763552731459) * 10 ^ 70 +
        8391385361892477194833928194973918710269696786622236682303562407096479) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 359 = 186 +
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
    rw [show 77 = 9 +
      68 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_358_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_358_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_359_prefix_zero :
    (∑ x ∈ Finset.range 187,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (359 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (359 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_359_suffix_zero :
    (∑ x ∈ Finset.range 69,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (359 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_359 :
    recurrence5Scalar1Left.coeff 359 =
      (((((9793457832409785923163180481174965992812 * 10 ^ 70 +
        5389499047875388118058896474590732595598068004322406645086476240992048) * 10 ^ 70 +
        0899600007187820323548336728891900797566093343203763755643025447178169) * 10 ^ 70 +
        7776100507768805930913067227733576544546637318950667563817124350691105) * 10 ^ 70 +
        4043357364332391700345595035869128841951013453709766926757179178181269) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 360 = 187 +
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
    rw [show 77 = 8 +
      69 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_359_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_359_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_360_prefix_zero :
    (∑ x ∈ Finset.range 188,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (360 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (360 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_360_suffix_zero :
    (∑ x ∈ Finset.range 70,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (360 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_360 :
    recurrence5Scalar1Left.coeff 360 =
      -(((((4136937818635763797696802309681204977757 * 10 ^ 70 +
        4450989599011028766455076412721413753343418564443130074942608520753685) * 10 ^ 70 +
        1738519656469577801749320164901873255750740299291303221332778823771395) * 10 ^ 70 +
        5445503658623425347760012564055976106318339781880763598850519325380460) * 10 ^ 70 +
        3219362918180990637372503686273851231751010265106232125747020283498023) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 361 = 188 +
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
    rw [show 77 = 7 +
      70 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_360_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_360_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_361_prefix_zero :
    (∑ x ∈ Finset.range 189,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (361 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (361 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_361_suffix_zero :
    (∑ x ∈ Finset.range 71,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (361 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_361 :
    recurrence5Scalar1Left.coeff 361 =
      (((((1660220565729819849552820720492097893569 * 10 ^ 70 +
        5021067607648092657703229025962422627178412495379042305253940553403653) * 10 ^ 70 +
        8695520376948709886372436376612237297814169310998396975275923513154027) * 10 ^ 70 +
        1961781917358914880540116484384698031219186352035413829888788899281815) * 10 ^ 70 +
        0958749989075188204429762401486804165073539797921853129556017350180013) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 362 = 189 +
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
    rw [show 77 = 6 +
      71 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_361_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_361_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_362_prefix_zero :
    (∑ x ∈ Finset.range 190,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (362 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (362 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_362_suffix_zero :
    (∑ x ∈ Finset.range 72,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (362 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_362 :
    recurrence5Scalar1Left.coeff 362 =
      -(((((641613328242385320762537073669991536049 * 10 ^ 70 +
        6564367506786902254587721542114171382887850088782458167990941596393361) * 10 ^ 70 +
        7505224339333195705474017013040761459824254627858524901414684161958622) * 10 ^ 70 +
        3816371641365134612214948669291396930434911318620866435499057287766390) * 10 ^ 70 +
        7394634553429546477445276792913340529801572794583984253854538132005054) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 363 = 190 +
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
    rw [show 77 = 5 +
      72 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_362_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_362_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_363_prefix_zero :
    (∑ x ∈ Finset.range 191,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (363 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (363 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_363_suffix_zero :
    (∑ x ∈ Finset.range 73,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (363 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_363 :
    recurrence5Scalar1Left.coeff 363 =
      (((((240575339655040423836004989957742253844 * 10 ^ 70 +
        2629553790967083949763544266867029221695893379788705237545004224593576) * 10 ^ 70 +
        9596932486443446662485645453676284725847060475784141097817621897981351) * 10 ^ 70 +
        5465583907631927194372701709669034278517901539203195613878139480414549) * 10 ^ 70 +
        1735450254967248072047321561899361506705310942370492189272876562348692) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 364 = 191 +
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
    rw [show 77 = 4 +
      73 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_363_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_363_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_364_prefix_zero :
    (∑ x ∈ Finset.range 192,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (364 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (364 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_364_suffix_zero :
    (∑ x ∈ Finset.range 74,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (364 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_364 :
    recurrence5Scalar1Left.coeff 364 =
      -(((((87876889928687843512368202434951590184 * 10 ^ 70 +
        1648182780788418213378402872897260856111157196205082009943605801649898) * 10 ^ 70 +
        0265661618406367099668313121736306670871460842096050608798382036158830) * 10 ^ 70 +
        0004612330485515164649535492780313216937316991154585361531901101298302) * 10 ^ 70 +
        8851309001802759693282995032472023733104003931733896498804294477188191) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 365 = 192 +
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
    rw [show 77 = 3 +
      74 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_364_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_364_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_365_prefix_zero :
    (∑ x ∈ Finset.range 193,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (365 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (365 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_365_suffix_zero :
    (∑ x ∈ Finset.range 75,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (365 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_365 :
    recurrence5Scalar1Left.coeff 365 =
      (((((31334180321184251470035756782066006057 * 10 ^ 70 +
        9540864088826578074286335993674029404749824696062231627574583702910411) * 10 ^ 70 +
        7750484202277110569998335093222970477317656667960276686122049005901753) * 10 ^ 70 +
        2608129576334036742137762960639152343968767857670082354292207637130402) * 10 ^ 70 +
        3373133614698884298503870474234534085464669541153305874864568794763156) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 366 = 193 +
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
    rw [show 77 = 2 +
      75 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_365_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_365_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_366_prefix_zero :
    (∑ x ∈ Finset.range 194,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (366 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (366 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_366_suffix_zero :
    (∑ x ∈ Finset.range 76,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (366 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_366 :
    recurrence5Scalar1Left.coeff 366 =
      -(((((10914314433563262719852112547743475873 * 10 ^ 70 +
        9068948518725286859901779720166993924232188444535401832306121533903394) * 10 ^ 70 +
        8198235761528262959020473579837384694169802346472265267541090203616838) * 10 ^ 70 +
        7145325656393898933270259228403883810650660428722499434598841261589440) * 10 ^ 70 +
        8808873839771108309535620333881693866849820973042782929266390039387719) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 367 = 194 +
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
    rw [show 77 = 1 +
      76 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_366_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_366_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_367_prefix_zero :
    (∑ x ∈ Finset.range 195,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (367 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (367 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_367_suffix_zero :
    (∑ x ∈ Finset.range 77,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (367 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_367 :
    recurrence5Scalar1Left.coeff 367 =
      (((((3713603709725455297803652821111015241 * 10 ^ 70 +
        7537210941254380445828874855904366081992185921127881983260134237628538) * 10 ^ 70 +
        2799071009820820005823538436886685573380708303880705142089593406319195) * 10 ^ 70 +
        7327714773517041549000717345454534592143436553306283191686526072606000) * 10 ^ 70 +
        0937051238409022915025016824002315085915250096416767230029439422855497) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 368 = 195 +
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
  rw [recurrence5Scalar1Left_coeff_367_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_367_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_368_prefix_zero :
    (∑ x ∈ Finset.range 196,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (368 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (368 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_368_suffix_zero :
    (∑ x ∈ Finset.range 78,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (368 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_368 :
    recurrence5Scalar1Left.coeff 368 =
      -(((((1233783626150652321311784719565995032 * 10 ^ 70 +
        0042673959187126835422307568769319916818627593951884138383000628378946) * 10 ^ 70 +
        6106164496738029710196402014046080089197872095224195092091646330798440) * 10 ^ 70 +
        7257661234082779548214032734323811029893598038913903285691204942445841) * 10 ^ 70 +
        0376148616472049598541597348030533490105890947350535781191920120154060) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 369 = 196 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 31 +
      78 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_368_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_368_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_369_prefix_zero :
    (∑ x ∈ Finset.range 197,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (369 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (369 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_369_suffix_zero :
    (∑ x ∈ Finset.range 79,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (369 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_369 :
    recurrence5Scalar1Left.coeff 369 =
      (((((400036585097732930029921998873932282 * 10 ^ 70 +
        9000881879690787071252431315038989374682549214570339511354110107691164) * 10 ^ 70 +
        1226528630025374385667082135227976164530166043733813273391624837972199) * 10 ^ 70 +
        7569876599950631811835439885169432184861700851611991660647247341772779) * 10 ^ 70 +
        7584106414597579156203428075260170317207937035077168919271140861401068) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 370 = 197 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 30 +
      79 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_369_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_369_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_370_prefix_zero :
    (∑ x ∈ Finset.range 198,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (370 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (370 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_370_suffix_zero :
    (∑ x ∈ Finset.range 80,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (370 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_370 :
    recurrence5Scalar1Left.coeff 370 =
      -(((((126522580743550842317491954979268465 * 10 ^ 70 +
        2648776787647298024717974761137058238773207142052128433836097922434592) * 10 ^ 70 +
        9061889262885103883738262738800412946592131376076683270633272110661274) * 10 ^ 70 +
        2730390270530228880892480832486735115831394001228811468245230664091084) * 10 ^ 70 +
        8640877498012873847656919086690425595783200476141212716590336256406067) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 371 = 198 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 29 +
      80 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_370_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_370_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_371_prefix_zero :
    (∑ x ∈ Finset.range 199,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (371 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (371 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_371_suffix_zero :
    (∑ x ∈ Finset.range 81,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (371 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_371 :
    recurrence5Scalar1Left.coeff 371 =
      (((((39019398773674652472195967862296004 * 10 ^ 70 +
        9918434941587764870299151963078713471228098112144591950376291040754193) * 10 ^ 70 +
        5323841260184540908864629327640367026538174830362370328279081732029103) * 10 ^ 70 +
        0053326747956035651861879255877106789323799070160845995227006498754841) * 10 ^ 70 +
        3386920538197082909735436797368812882004042799620113817854206628045237) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 372 = 199 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 28 +
      81 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_371_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_371_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_372_prefix_zero :
    (∑ x ∈ Finset.range 200,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (372 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (372 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_372_suffix_zero :
    (∑ x ∈ Finset.range 82,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (372 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_372 :
    recurrence5Scalar1Left.coeff 372 =
      -(((((11730459374696253380553696226982337 * 10 ^ 70 +
        4309490843513534290198697838891598560289773875583530702242460751724322) * 10 ^ 70 +
        9558361501929902733267657842957087475835256863536007400290875171235011) * 10 ^ 70 +
        6574004179703448094957472544457468663094498984992442465734451434100669) * 10 ^ 70 +
        7397068959867753493225154826313263929698519255726301827269997172386654) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 373 = 200 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 27 +
      82 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_372_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_372_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_373_prefix_zero :
    (∑ x ∈ Finset.range 201,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (373 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (373 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_373_suffix_zero :
    (∑ x ∈ Finset.range 83,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (373 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_373 :
    recurrence5Scalar1Left.coeff 373 =
      (((((3436816411934644246717275766157104 * 10 ^ 70 +
        8917171609800132423046173758468411797071908678656802320671939818642479) * 10 ^ 70 +
        7668947152644314411284719629120096552754021681225831136308435113651172) * 10 ^ 70 +
        0983636672291611592026062877579155046638977816321758052329935045757510) * 10 ^ 70 +
        3670370120976353888763488268470293440622303123985966178695875226070372) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 374 = 201 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 26 +
      83 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_373_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_373_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_374_prefix_zero :
    (∑ x ∈ Finset.range 202,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (374 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (374 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_374_suffix_zero :
    (∑ x ∈ Finset.range 84,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (374 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_374 :
    recurrence5Scalar1Left.coeff 374 =
      -(((((980933044216081077026385079510472 * 10 ^ 70 +
        4541742072102705138128126047898476604041150523441061079877885341187813) * 10 ^ 70 +
        2400464005204817039897307037216602511507367435364569260132768412974401) * 10 ^ 70 +
        7060506957589779572705043815688121350338495327096358250117366999423851) * 10 ^ 70 +
        2269237211634107974264597244986680591466179722040128997852008496426068) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 375 = 202 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 25 +
      84 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_374_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_374_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_375_prefix_zero :
    (∑ x ∈ Finset.range 203,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (375 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (375 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_375_suffix_zero :
    (∑ x ∈ Finset.range 85,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (375 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_375 :
    recurrence5Scalar1Left.coeff 375 =
      (((((272567888365058513246187906171570 * 10 ^ 70 +
        4429219027925643926156419846144746299973852893830938450133032593164774) * 10 ^ 70 +
        2166402074087783958868885127265171140126203444799095138021047221849210) * 10 ^ 70 +
        9258479663291832408367280735287595644682132672110899995505369020405449) * 10 ^ 70 +
        6878213957973505930372998000081965096242579600300596189452131053209334) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 376 = 203 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 24 +
      85 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_375_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_375_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_376_prefix_zero :
    (∑ x ∈ Finset.range 204,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (376 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (376 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_376_suffix_zero :
    (∑ x ∈ Finset.range 86,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (376 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_376 :
    recurrence5Scalar1Left.coeff 376 =
      -(((((73648839813034753863003025960030 * 10 ^ 70 +
        6748029331004936614745500118631986976400963043525212164971394868797985) * 10 ^ 70 +
        0285523269287658365218776027341280803832330704610702686758652386921717) * 10 ^ 70 +
        7893218324985158745083176377303513091972193522540857928913508234243168) * 10 ^ 70 +
        2466869455158758952024277116320839433087384321365663505453866482177302) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 377 = 204 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 23 +
      86 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_376_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_376_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_377_prefix_zero :
    (∑ x ∈ Finset.range 205,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (377 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (377 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_377_suffix_zero :
    (∑ x ∈ Finset.range 87,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (377 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_377 :
    recurrence5Scalar1Left.coeff 377 =
      (((((19316437400653853089425130496406 * 10 ^ 70 +
        3492505585381491200833392373874304347571337454275927107772304918076013) * 10 ^ 70 +
        9678690394385976915284582769054128432849002140405188766597483618912017) * 10 ^ 70 +
        1540486088922771141185313594611567858640698363179130958581003896478306) * 10 ^ 70 +
        9364113355120468790973689546787289751520608935339349776352737249882913) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 378 = 205 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 22 +
      87 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_377_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_377_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_378_prefix_zero :
    (∑ x ∈ Finset.range 206,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (378 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (378 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_378_suffix_zero :
    (∑ x ∈ Finset.range 88,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (378 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_378 :
    recurrence5Scalar1Left.coeff 378 =
      -(((((4904611382140538078324919387459 * 10 ^ 70 +
        6395843703148265895793516145999432305232749892692889476467482915888737) * 10 ^ 70 +
        8332744882154738558614255059037073885802048858425370672119485259702274) * 10 ^ 70 +
        9943824538444216677472860551788017600601845206615501237440268912082101) * 10 ^ 70 +
        9092460166241103745064615596926093502658133006034452487797927766797362) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 379 = 206 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 21 +
      88 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_378_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_378_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_379_prefix_zero :
    (∑ x ∈ Finset.range 207,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (379 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (379 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_379_suffix_zero :
    (∑ x ∈ Finset.range 89,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (379 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_379 :
    recurrence5Scalar1Left.coeff 379 =
      (((((1201151190376822351338224530689 * 10 ^ 70 +
        3132781881939887398909614760886350669827709869007350740399069863664358) * 10 ^ 70 +
        8481618261707602844075282457898554271627918094688543284124674241198882) * 10 ^ 70 +
        1236352106492539578851191873762299341201386675458751570791371741527947) * 10 ^ 70 +
        4279860131106529177384405487293696950081543893250033461122083229147423) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 380 = 207 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 20 +
      89 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_379_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_379_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_380_prefix_zero :
    (∑ x ∈ Finset.range 208,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (380 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (380 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_380_suffix_zero :
    (∑ x ∈ Finset.range 90,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (380 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_380 :
    recurrence5Scalar1Left.coeff 380 =
      -(((((282322071700368047678472522981 * 10 ^ 70 +
        8106197023669522694359510911460174103076140582839663176294274395741145) * 10 ^ 70 +
        8152287052137694272817284722705290149855264080817973400936860089270348) * 10 ^ 70 +
        0549267610402471628579588469987864064344345379827864116383977624347536) * 10 ^ 70 +
        1990923503128130320676938546546032452514280309140912661456151085372026) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 381 = 208 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 19 +
      90 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_380_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_380_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_381_prefix_zero :
    (∑ x ∈ Finset.range 209,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (381 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (381 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_381_suffix_zero :
    (∑ x ∈ Finset.range 91,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (381 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_381 :
    recurrence5Scalar1Left.coeff 381 =
      (((((63255867244127372681371096372 * 10 ^ 70 +
        7266406962810475882099937102079228468794640529124424715565395750706937) * 10 ^ 70 +
        4703162738612338841220853364215745069134804581519122423884970285791287) * 10 ^ 70 +
        2307337918109293637932626635565370408573911679668041994752021784269546) * 10 ^ 70 +
        8642226644165373871993905081724285935932346149054299967797556571411173) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 382 = 209 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 18 +
      91 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_381_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_381_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_382_prefix_zero :
    (∑ x ∈ Finset.range 210,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (382 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (382 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_382_suffix_zero :
    (∑ x ∈ Finset.range 92,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (382 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_382 :
    recurrence5Scalar1Left.coeff 382 =
      -(((((13378934859404564734176370727 * 10 ^ 70 +
        6078332176455973499580847737725780106980473245299256541928636810982462) * 10 ^ 70 +
        1022251951224907040997511333210820812850248159412551711683760812550813) * 10 ^ 70 +
        2033018916524419163902858241253669667178117725244337529456329514614034) * 10 ^ 70 +
        3076059073462762430081958084538670008349958802485483709903528814172800) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 383 = 210 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 17 +
      92 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_382_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_382_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_383_prefix_zero :
    (∑ x ∈ Finset.range 211,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (383 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (383 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_383_suffix_zero :
    (∑ x ∈ Finset.range 93,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (383 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_383 :
    recurrence5Scalar1Left.coeff 383 =
      (((((2629609850465823496188537905 * 10 ^ 70 +
        7035941329064015024310902093694051178112314049161689133620192323588769) * 10 ^ 70 +
        7515346936329309114785532779459365384504951666904512161879447556987100) * 10 ^ 70 +
        2157825759396527347267221318482296900299986177451054728125846978300818) * 10 ^ 70 +
        3690858042049271592143862656290661640427863158490915364558293470043288) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 384 = 211 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 16 +
      93 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_383_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_383_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_384_prefix_zero :
    (∑ x ∈ Finset.range 212,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (384 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (384 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_384_suffix_zero :
    (∑ x ∈ Finset.range 94,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (384 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_384 :
    recurrence5Scalar1Left.coeff 384 =
      -(((((466261693765019170167920113 * 10 ^ 70 +
        3532571302540245554538455758643922060348497194265392644086041265709183) * 10 ^ 70 +
        0639539294815680047956667734010682971819779481972582919845836450628443) * 10 ^ 70 +
        3970592464293506079022449886816613907891033195500892271223067341162090) * 10 ^ 70 +
        1149684577903338377587039484575625441375213425228157423553046678471130) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 385 = 212 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 15 +
      94 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_384_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_384_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_385_prefix_zero :
    (∑ x ∈ Finset.range 213,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (385 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (385 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_385_suffix_zero :
    (∑ x ∈ Finset.range 95,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (385 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_385 :
    recurrence5Scalar1Left.coeff 385 =
      (((((69452065971158000804151898 * 10 ^ 70 +
        7030506033802691637516684628773880188670232738032613042755439376777856) * 10 ^ 70 +
        7696318130327967079267639913397576007735116751302177515278161643618353) * 10 ^ 70 +
        1710095863029816387137820965500392552198873736048679681867044974077038) * 10 ^ 70 +
        8099274727967861920083063619517835104792031167706909423066814026328176) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 386 = 213 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 14 +
      95 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_385_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_385_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_386_prefix_zero :
    (∑ x ∈ Finset.range 214,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (386 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (386 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_386_suffix_zero :
    (∑ x ∈ Finset.range 96,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (386 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_386 :
    recurrence5Scalar1Left.coeff 386 =
      -(((((6606257149333076430010034 * 10 ^ 70 +
        1651194645687053409649703017233793392665822676403952658951938727436765) * 10 ^ 70 +
        4273142730801425895527157319179591699593535811044073578754062546542231) * 10 ^ 70 +
        3462440591017303095931531516218908559200233614507653992664871048808756) * 10 ^ 70 +
        7310706379762088435191429843901781367170697759297800659725763526077379) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 387 = 214 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 13 +
      96 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_386_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_386_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_387_prefix_zero :
    (∑ x ∈ Finset.range 215,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (387 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (387 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_387_suffix_zero :
    (∑ x ∈ Finset.range 97,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (387 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_387 :
    recurrence5Scalar1Left.coeff 387 =
      -(((((612510419262820146229730 * 10 ^ 70 +
        0786234258129649174946931506405560949252971460972567391282686350959520) * 10 ^ 70 +
        7749577561561419819349662055593828550323050072559209364832927475388706) * 10 ^ 70 +
        6198759664672037437742632395060674389737248285826091391171820957225206) * 10 ^ 70 +
        5357563378545513334584311266204119986965147519100365277048120784892347) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 388 = 215 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 12 +
      97 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_387_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_387_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_388_prefix_zero :
    (∑ x ∈ Finset.range 216,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (388 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (388 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_388_suffix_zero :
    (∑ x ∈ Finset.range 98,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (388 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_388 :
    recurrence5Scalar1Left.coeff 388 =
      (((((582881214035985898466291 * 10 ^ 70 +
        5979415355123692085127496957203065497893359465254872022743879264922084) * 10 ^ 70 +
        0177579761140121386011815615534428553925069209989100592030795336572305) * 10 ^ 70 +
        7023640953640377746331006585118300542928492119204258893206675731201118) * 10 ^ 70 +
        8806785963357168791089532897182420342850219430896371209360596808937274) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 389 = 216 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 11 +
      98 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_388_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_388_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_389_prefix_zero :
    (∑ x ∈ Finset.range 217,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (389 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (389 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_389_suffix_zero :
    (∑ x ∈ Finset.range 99,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (389 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_389 :
    recurrence5Scalar1Left.coeff 389 =
      -(((((214521427305449922583239 * 10 ^ 70 +
        6026890383289308941519787236183006348308198821510317858369452127565891) * 10 ^ 70 +
        7870444894590702070649289165250548348002065423866364547223251531135144) * 10 ^ 70 +
        3469439189843033930080742294540633131611175990823810339651420689294317) * 10 ^ 70 +
        1046172996230727912714184845665268989970446113524735238674668966459112) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 390 = 217 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 10 +
      99 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_389_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_389_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_390_prefix_zero :
    (∑ x ∈ Finset.range 218,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (390 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (390 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_390_suffix_zero :
    (∑ x ∈ Finset.range 100,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (390 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_390 :
    recurrence5Scalar1Left.coeff 390 =
      (((((60748670371326915180694 * 10 ^ 70 +
        0447538073946851088761980541367398943191683844179516229776854044716636) * 10 ^ 70 +
        9282789689710158270535815872458204375463813690085258050149338821795125) * 10 ^ 70 +
        6223108104026845694069571487468892215978492844840903233565573048179783) * 10 ^ 70 +
        8635092940619123711960371259032112741907757256909815639631664545958715) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 391 = 218 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 9 +
      100 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_390_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_390_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_391_prefix_zero :
    (∑ x ∈ Finset.range 219,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (391 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (391 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_391_suffix_zero :
    (∑ x ∈ Finset.range 101,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (391 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_391 :
    recurrence5Scalar1Left.coeff 391 =
      -(((((14549769022645328482436 * 10 ^ 70 +
        3190473908029037749280662038677084053096694858456513182108336806510588) * 10 ^ 70 +
        8569307403988806416304048965448005494733881031155728743226573067277600) * 10 ^ 70 +
        2040312944476918302217974064341708711372199994396722440017386096655819) * 10 ^ 70 +
        8472363631159949103760668950956718845730523982978720856261246006559751) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 392 = 219 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 8 +
      101 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_391_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_391_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_392_prefix_zero :
    (∑ x ∈ Finset.range 220,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (392 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (392 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_392_suffix_zero :
    (∑ x ∈ Finset.range 102,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (392 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_392 :
    recurrence5Scalar1Left.coeff 392 =
      (((((2962484703701623791086 * 10 ^ 70 +
        3165614918442272268307641835453974413161120569183284543086130513735583) * 10 ^ 70 +
        8134048635334953548729536260317914239891114544903063654249331342085720) * 10 ^ 70 +
        1615635687933217686533245761378046389297404096567266388304703105835482) * 10 ^ 70 +
        6851712450986590136323832149884960435773175949161975202694368655044864) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 393 = 220 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 7 +
      102 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_392_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_392_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_393_prefix_zero :
    (∑ x ∈ Finset.range 221,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (393 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (393 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_393_suffix_zero :
    (∑ x ∈ Finset.range 103,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (393 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_393 :
    recurrence5Scalar1Left.coeff 393 =
      -(((((481371134112831498871 * 10 ^ 70 +
        5795633968357586412474050379455329774819055488186607934029336331180366) * 10 ^ 70 +
        7546196207607942745964634844962830360294105316261957539501768078002626) * 10 ^ 70 +
        1399404701859766965213587747878058920453936791163575515761553126454744) * 10 ^ 70 +
        2705689139339060651915454933581596182998649649286274488004790236076511) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 394 = 221 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 6 +
      103 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_393_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_393_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_394_prefix_zero :
    (∑ x ∈ Finset.range 222,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (394 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (394 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_394_suffix_zero :
    (∑ x ∈ Finset.range 104,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (394 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_394 :
    recurrence5Scalar1Left.coeff 394 =
      (((((45652319673148126336 * 10 ^ 70 +
        3524491792468885969920877517128455364316205308964264774596014504241319) * 10 ^ 70 +
        2710884723924138415493719709543264606902232192894227993417874456939156) * 10 ^ 70 +
        7677609236519889427589505013880563523904188927649069298484782888411859) * 10 ^ 70 +
        3004516874337742757079073302733155828489063177670734048089104997785471) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 395 = 222 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 5 +
      104 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_394_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_394_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_395_prefix_zero :
    (∑ x ∈ Finset.range 223,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (395 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (395 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_395_suffix_zero :
    (∑ x ∈ Finset.range 105,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (395 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_395 :
    recurrence5Scalar1Left.coeff 395 =
      (((((6228088493308219812 * 10 ^ 70 +
        7238842978637069207437379215861198393145824974426640636602019789726395) * 10 ^ 70 +
        6630371850947778080439930052022954871139098841219227393486896816109008) * 10 ^ 70 +
        7571502505876598841602509556867017105246237243519790390676034883696938) * 10 ^ 70 +
        7300059601832853332815386520516073628009842053733236546490475650273715) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 396 = 223 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 4 +
      105 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_395_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_395_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_396_prefix_zero :
    (∑ x ∈ Finset.range 224,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (396 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (396 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_396_suffix_zero :
    (∑ x ∈ Finset.range 106,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (396 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_396 :
    recurrence5Scalar1Left.coeff 396 =
      -(((((4908463235894551130 * 10 ^ 70 +
        2601858803526678896681085600149580970063271593855035994023650522129145) * 10 ^ 70 +
        5521557506227850440525867433011365669714022708754141768538138805551234) * 10 ^ 70 +
        5797664489685670146826720015492925807927844729066126139989882795238406) * 10 ^ 70 +
        5308256199885016136720515538500471222806613766843285496401443425017543) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 397 = 224 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 3 +
      106 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_396_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_396_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_397_prefix_zero :
    (∑ x ∈ Finset.range 225,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (397 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (397 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_397_suffix_zero :
    (∑ x ∈ Finset.range 107,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (397 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_397 :
    recurrence5Scalar1Left.coeff 397 =
      (((((1658444087841711394 * 10 ^ 70 +
        2009867004917463681289851281196218162152271138987839179174994814118701) * 10 ^ 70 +
        2686613164154565159616661068263870831245508824953130295275319634486820) * 10 ^ 70 +
        0422664525554736567967910382613161192010014642713187270422258939936071) * 10 ^ 70 +
        6671734606885984776609404162737608842798583453752747959081639288959884) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 398 = 225 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 2 +
      107 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_397_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_397_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_398_prefix_zero :
    (∑ x ∈ Finset.range 226,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (398 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (398 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_398_suffix_zero :
    (∑ x ∈ Finset.range 108,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (398 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_398 :
    recurrence5Scalar1Left.coeff 398 =
      -(((((408904350559108819 * 10 ^ 70 +
        3863494646863971872063384033502813437582612102514425115172680202141131) * 10 ^ 70 +
        0291969669874697232382026900402729600499095838457350619240579701334119) * 10 ^ 70 +
        8586669689191617766160776136021098570966922128029839109003864800722961) * 10 ^ 70 +
        9601825277649704625996138308608571785717304426012246422199040369523290) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 399 = 226 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 1 +
      108 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_398_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_398_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_399_prefix_zero :
    (∑ x ∈ Finset.range 227,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (399 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (399 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_399_suffix_zero :
    (∑ x ∈ Finset.range 109,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (399 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_399 :
    recurrence5Scalar1Left.coeff 399 =
      (((((76642316891350236 * 10 ^ 70 +
        7442948796681071904467495959333562305262922617600471575954110545063061) * 10 ^ 70 +
        5183468841557407894028079647585978505408650022270738938789648403082263) * 10 ^ 70 +
        0154501061166833528551197482251823282993830816703964866691927927925549) * 10 ^ 70 +
        9428522120791520339099638729163940661665698138179619282848122124127832) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 400 = 227 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_399_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_399_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_400_prefix_zero :
    (∑ x ∈ Finset.range 228,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (400 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (400 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_400_suffix_zero :
    (∑ x ∈ Finset.range 110,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (400 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_400 :
    recurrence5Scalar1Left.coeff 400 =
      -(((((9418137388311143 * 10 ^ 70 +
        4976012256128429150827074638802971086538770072253937173609728408063753) * 10 ^ 70 +
        8097170002060363332297460626339335003852513115039375767372398197346200) * 10 ^ 70 +
        3010587373500920269107553907667967668859808897892623189289269194488098) * 10 ^ 70 +
        3790762968766309291928908427443890336108178938596563011728301562486866) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 401 = 228 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 31 +
      110 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_400_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_400_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_401_prefix_zero :
    (∑ x ∈ Finset.range 229,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (401 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (401 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_401_suffix_zero :
    (∑ x ∈ Finset.range 111,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (401 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_401 :
    recurrence5Scalar1Left.coeff 401 =
      -(((((44187245432112 * 10 ^ 70 +
        9848916859443042050358812002971472559161099129916435632042721158353017) * 10 ^ 70 +
        7763295220107540962581002432957614402207561349267249084090101705099671) * 10 ^ 70 +
        2383815699903130193582937035965174436918314318390493604385223556768444) * 10 ^ 70 +
        8652853459118100948023216454946527272553647733394687081118851785645274) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 402 = 229 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 30 +
      111 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_401_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_401_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_402_prefix_zero :
    (∑ x ∈ Finset.range 230,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (402 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (402 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_402_suffix_zero :
    (∑ x ∈ Finset.range 112,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (402 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_402 :
    recurrence5Scalar1Left.coeff 402 =
      (((((414729752534650 * 10 ^ 70 +
        8262542912110878368039415612782590484557214209589825781945273853799303) * 10 ^ 70 +
        2426082872228584225871495176368993718457946858719028549055006223793180) * 10 ^ 70 +
        1064116377220602516605780063940785521906257825034030263758340672294094) * 10 ^ 70 +
        0084431495245399863086871539723265239770851895816842939554759461406271) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 403 = 230 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 29 +
      112 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_402_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_402_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_403_prefix_zero :
    (∑ x ∈ Finset.range 231,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (403 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (403 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_403_suffix_zero :
    (∑ x ∈ Finset.range 113,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (403 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_403 :
    recurrence5Scalar1Left.coeff 403 =
      -(((((134960741788355 * 10 ^ 70 +
        0011770578834253909989915968064810764524237118617431277540613190879013) * 10 ^ 70 +
        5166080074516421430193402757590950710155705500493841330124977824758773) * 10 ^ 70 +
        4581294249798559641211602757763282271897622000980163199563935109783445) * 10 ^ 70 +
        1480016996361048493770580895127590220374680554614867754253788315348210) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 404 = 231 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 28 +
      113 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_403_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_403_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_404_prefix_zero :
    (∑ x ∈ Finset.range 232,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (404 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (404 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_404_suffix_zero :
    (∑ x ∈ Finset.range 114,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (404 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_404 :
    recurrence5Scalar1Left.coeff 404 =
      (((((26834327814991 * 10 ^ 70 +
        6222218833784505982685329140090354475791550702290080343775365288699945) * 10 ^ 70 +
        5519178135391311581295443674811840637583921534976769895475207035781561) * 10 ^ 70 +
        5551102967930757785695805170260510862686510822161428751965947477621269) * 10 ^ 70 +
        5926897068895712846585713313391319339886570973901269751220887251309240) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 405 = 232 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 27 +
      114 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_404_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_404_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_405_prefix_zero :
    (∑ x ∈ Finset.range 233,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (405 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (405 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_405_suffix_zero :
    (∑ x ∈ Finset.range 115,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (405 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_405 :
    recurrence5Scalar1Left.coeff 405 =
      -(((((3264909632374 * 10 ^ 70 +
        5521526194826236463665756921829880592429841652005482312785674308053593) * 10 ^ 70 +
        5064221594426210359651252559456801462665554451834285466606016223397599) * 10 ^ 70 +
        4587399817647733789695190366988376077971997154857628513701670876846829) * 10 ^ 70 +
        4475189903260900317166581500995838612102043492123739825935783951259914) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 406 = 233 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 26 +
      115 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_405_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_405_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_406_prefix_zero :
    (∑ x ∈ Finset.range 234,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (406 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (406 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_406_suffix_zero :
    (∑ x ∈ Finset.range 116,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (406 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_406 :
    recurrence5Scalar1Left.coeff 406 =
      (((((36838593474 * 10 ^ 70 +
        8270656291508039217342951184500366207160988099180506300503943000864158) * 10 ^ 70 +
        8545895804384127492800182743951140293255917216396008894481626844638571) * 10 ^ 70 +
        4766340941323245315099172062761035794298931188230751550898734519395468) * 10 ^ 70 +
        2900714374447694296856375112137017605048479217896941805284117721313337) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 407 = 234 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 25 +
      116 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_406_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_406_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_407_prefix_zero :
    (∑ x ∈ Finset.range 235,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (407 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (407 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_407_suffix_zero :
    (∑ x ∈ Finset.range 117,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (407 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_407 :
    recurrence5Scalar1Left.coeff 407 =
      (((((93852078633 * 10 ^ 70 +
        1429989009418566954316587910378599529877466712334467052149321177739475) * 10 ^ 70 +
        9531545902727471437845157402974263762027384519382125064459232632301871) * 10 ^ 70 +
        9081730691757147284202079842206207545261044244757805726682867203396106) * 10 ^ 70 +
        4661434291607020274490044143358466381212894100320187580049412169550856) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 408 = 235 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 24 +
      117 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_407_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_407_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_408_prefix_zero :
    (∑ x ∈ Finset.range 236,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (408 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (408 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_408_suffix_zero :
    (∑ x ∈ Finset.range 118,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (408 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_408 :
    recurrence5Scalar1Left.coeff 408 =
      -(((((26128204758 * 10 ^ 70 +
        2312481776192919523915189259906482909353723783668648679904530945293801) * 10 ^ 70 +
        0986378355454987800565847098148298387391448138301225436436982512159406) * 10 ^ 70 +
        5442302346578888274773791363168475938130744251606982746312890829552054) * 10 ^ 70 +
        3113438980999733385534494584453514264349285653064307388408657317183928) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 409 = 236 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 23 +
      118 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_408_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_408_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_409_prefix_zero :
    (∑ x ∈ Finset.range 237,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (409 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (409 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_409_suffix_zero :
    (∑ x ∈ Finset.range 119,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (409 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_409 :
    recurrence5Scalar1Left.coeff 409 =
      (((((4069008522 * 10 ^ 70 +
        6897392526485571519902672572906958070107386651214526832441287466033275) * 10 ^ 70 +
        1733292688743751560296653798910712675595722833183661081718037001019797) * 10 ^ 70 +
        4455644196968738394436000511785886713414270808915309129189240863703177) * 10 ^ 70 +
        7287566360627455361666041252794808366193260402765199227233905679624053) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 410 = 237 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 22 +
      119 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_409_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_409_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_410_prefix_zero :
    (∑ x ∈ Finset.range 238,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (410 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (410 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_410_suffix_zero :
    (∑ x ∈ Finset.range 120,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (410 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_410 :
    recurrence5Scalar1Left.coeff 410 =
      -(((((324469797 * 10 ^ 70 +
        1569656019739763192619747157075466960752830953983615857041681362482129) * 10 ^ 70 +
        3279360314707998627455874333095893803897555521250018004040710735822597) * 10 ^ 70 +
        8191681572463163772917844373409481565593599272462584984437116082804835) * 10 ^ 70 +
        5167109183488978271732004525303603533801323485406247951111486324618269) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 411 = 238 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 21 +
      120 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_410_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_410_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_411_prefix_zero :
    (∑ x ∈ Finset.range 239,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (411 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (411 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_411_suffix_zero :
    (∑ x ∈ Finset.range 121,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (411 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_411 :
    recurrence5Scalar1Left.coeff 411 =
      -(((((19383656 * 10 ^ 70 +
        9999944154409132675208832537729315386550935445216696503533242626943908) * 10 ^ 70 +
        0343677495831983792013597384329042498080955307798824312476746981930956) * 10 ^ 70 +
        3376302873767311843975698680723450293009722032859864060616881169148193) * 10 ^ 70 +
        4884938545828906693942705833533912492712382330997423359770688357448569) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 412 = 239 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 20 +
      121 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_411_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_411_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_412_prefix_zero :
    (∑ x ∈ Finset.range 240,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (412 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (412 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_412_suffix_zero :
    (∑ x ∈ Finset.range 122,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (412 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_412 :
    recurrence5Scalar1Left.coeff 412 =
      (((((10901074 * 10 ^ 70 +
        0188927537005005160759523162292222581942125696910410138492659766378242) * 10 ^ 70 +
        5881674085202467350765754155389608386865604974671837541487409661133452) * 10 ^ 70 +
        4241498192025326381074706641296345439944299189316238691314779070067586) * 10 ^ 70 +
        7048543394993783933942488415391610248252347673753255266188859482587250) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 413 = 240 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 19 +
      122 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_412_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_412_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_413_prefix_zero :
    (∑ x ∈ Finset.range 241,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (413 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (413 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_413_suffix_zero :
    (∑ x ∈ Finset.range 123,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (413 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_413 :
    recurrence5Scalar1Left.coeff 413 =
      -(((((1814897 * 10 ^ 70 +
        2630099348748385108721287720350728891237300681882853808344482878833564) * 10 ^ 70 +
        2948536136674557721703152015227792311044567079794006842502952737802655) * 10 ^ 70 +
        0574581721999900474331904224254540147057464735028348053378995007414485) * 10 ^ 70 +
        7108180218425120840589192334798527922062728897603310009933418245323648) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 414 = 241 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 18 +
      123 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_413_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_413_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_414_prefix_zero :
    (∑ x ∈ Finset.range 242,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (414 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (414 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_414_suffix_zero :
    (∑ x ∈ Finset.range 124,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (414 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_414 :
    recurrence5Scalar1Left.coeff 414 =
      (((((151020 * 10 ^ 70 +
        1595573375889849056585913462598114316826844090476954758801395542657334) * 10 ^ 70 +
        0388528170274971716455218294427562481059042309661234001606000125900348) * 10 ^ 70 +
        2030632999382970973691527374664009333367009076795836677408923139738420) * 10 ^ 70 +
        5030907863393855159967522456387962786534003855545678017890554570185191) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 415 = 242 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 17 +
      124 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_414_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_414_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_415_prefix_zero :
    (∑ x ∈ Finset.range 243,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (415 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (415 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_415_suffix_zero :
    (∑ x ∈ Finset.range 125,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (415 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_415 :
    recurrence5Scalar1Left.coeff 415 =
      (((((2493 * 10 ^ 70 +
        2562105376534457120927275709362312784572941471347428383864816380734471) * 10 ^ 70 +
        9299615698083578417651463994255009303326211962512459122120410433696391) * 10 ^ 70 +
        5873487053288216649908443598999296436899464721546623318976229537263554) * 10 ^ 70 +
        4699962059039061418323149259388769877273616638828430378162059459901115) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 416 = 243 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 16 +
      125 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_415_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_415_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_416_prefix_zero :
    (∑ x ∈ Finset.range 244,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (416 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (416 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_416_suffix_zero :
    (∑ x ∈ Finset.range 126,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (416 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_416 :
    recurrence5Scalar1Left.coeff 416 =
      -(((((2678 * 10 ^ 70 +
        7982965191635102721347484982645344944534362703223348158467536302447395) * 10 ^ 70 +
        4991606577705177382305591603640643049585886574300852495025853265664080) * 10 ^ 70 +
        5088198032943938589465976592406890025312557778960662288925372810653687) * 10 ^ 70 +
        6731612069332389493594696793297909289785496264937561656983314972908069) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 417 = 244 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 15 +
      126 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_416_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_416_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_417_prefix_zero :
    (∑ x ∈ Finset.range 245,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (417 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (417 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_417_suffix_zero :
    (∑ x ∈ Finset.range 127,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (417 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_417 :
    recurrence5Scalar1Left.coeff 417 =
      (((((396 * 10 ^ 70 +
        5881075126336360972853450119550091963191134977131517793670708816258408) * 10 ^ 70 +
        1592237092891232816515837188638120261611981066274882731684945304414292) * 10 ^ 70 +
        3577083261385912027876001712985455701716707257876409735305920839536328) * 10 ^ 70 +
        9561680664891588869477082626051093079425643532655891339495139057637781) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 418 = 245 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 14 +
      127 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_417_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_417_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_418_prefix_zero :
    (∑ x ∈ Finset.range 246,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (418 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (418 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_418_suffix_zero :
    (∑ x ∈ Finset.range 128,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (418 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_418 :
    recurrence5Scalar1Left.coeff 418 =
      -(((((27 * 10 ^ 70 +
        6160425941282059946734462427203983394018736965496585792127480356017987) * 10 ^ 70 +
        7649044658390421755269280111334616456862564315455159134795750070069124) * 10 ^ 70 +
        8619974291340889774884719870171673508534971081097795784791763889158391) * 10 ^ 70 +
        6113584644553899018221615987467431003868687844707696367569849534338743) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 419 = 246 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 13 +
      128 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_418_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_418_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_419_prefix_zero :
    (∑ x ∈ Finset.range 247,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (419 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (419 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_419_suffix_zero :
    (∑ x ∈ Finset.range 129,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (419 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_419 :
    recurrence5Scalar1Left.coeff 419 =
      -((((2647273724837587750558770864507875821878369568734175384253183761232860 * 10 ^ 70 +
        6783222025195220003015230632843599522118699622739275658147993236179741) * 10 ^ 70 +
        0880285485586295636765501959888768638691725567598315525045332593405006) * 10 ^ 70 +
        5429321651201413615809910958968311664131087650121081812905905359821402) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 420 = 247 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 12 +
      129 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_419_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_419_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_420_prefix_zero :
    (∑ x ∈ Finset.range 248,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (420 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (420 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_420_suffix_zero :
    (∑ x ∈ Finset.range 130,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (420 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_420 :
    recurrence5Scalar1Left.coeff 420 =
      ((((2718180547843842873300354523288293095156268488258069214219822176727818 * 10 ^ 70 +
        2866570518183813076870357507789059773747632004236656744200956353920307) * 10 ^ 70 +
        5530738999895325176534585849293803849045537433334755014050414744165344) * 10 ^ 70 +
        7505539235659753418294886132759090212378827096127626143088875279552295) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 421 = 248 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 11 +
      130 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_420_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_420_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_421_prefix_zero :
    (∑ x ∈ Finset.range 249,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (421 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (421 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_421_suffix_zero :
    (∑ x ∈ Finset.range 131,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (421 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_421 :
    recurrence5Scalar1Left.coeff 421 =
      -((((275757207171202256761099383393686547945122119695622937117901147009891 * 10 ^ 70 +
        1170222594212522326217300390241072990673739954253676862483477314309890) * 10 ^ 70 +
        6074020831690164230066293334188965317903232081557103613362497382175274) * 10 ^ 70 +
        5346297868668591651049173171866488347488863785657668567697804464055694) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 422 = 249 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 10 +
      131 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_421_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_421_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_422_prefix_zero :
    (∑ x ∈ Finset.range 250,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (422 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (422 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_422_suffix_zero :
    (∑ x ∈ Finset.range 132,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (422 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_422 :
    recurrence5Scalar1Left.coeff 422 =
      ((((9227567575740418468793179167394745861419242703055284998466781172142 * 10 ^ 70 +
        3956667346873399297727295253385861003212327879465230919426840900614197) * 10 ^ 70 +
        2171300773020226666411129278588765512188235889674415375660838459020240) * 10 ^ 70 +
        9254053967694629566749478835302008139953350478498544769440678445752576) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 423 = 250 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 9 +
      132 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_422_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_422_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_423_prefix_zero :
    (∑ x ∈ Finset.range 251,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (423 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (423 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_423_suffix_zero :
    (∑ x ∈ Finset.range 133,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (423 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_423 :
    recurrence5Scalar1Left.coeff 423 =
      ((((710314450676213819159179662957965128118569214163934103233364368834 * 10 ^ 70 +
        5221328726380771794591959607879494086183095784823039115611271212213537) * 10 ^ 70 +
        3714781818797932874812604112494778727201984469158228713786364738548668) * 10 ^ 70 +
        7187940284378750192236803394255361001209140309602537550167412088416828) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 424 = 251 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 8 +
      133 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_423_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_423_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_424_prefix_zero :
    (∑ x ∈ Finset.range 252,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (424 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (424 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_424_suffix_zero :
    (∑ x ∈ Finset.range 134,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (424 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_424 :
    recurrence5Scalar1Left.coeff 424 =
      -((((93398295855387292494274264747046264777673674504340061452943856663 * 10 ^ 70 +
        0981636686520146084136602718005607120618232271230105986966842819799000) * 10 ^ 70 +
        5303016033454514133804360989064576981131748982079339427635977321591228) * 10 ^ 70 +
        1087378418679045419821095592025035995674177318192899051630144994610759) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 425 = 252 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 7 +
      134 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_424_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_424_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_425_prefix_zero :
    (∑ x ∈ Finset.range 253,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (425 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (425 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_425_suffix_zero :
    (∑ x ∈ Finset.range 135,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (425 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_425 :
    recurrence5Scalar1Left.coeff 425 =
      ((((3162152739211657394368158381366552909220559082729384668731051040 * 10 ^ 70 +
        2996632513524333780533306626092095184622130722681951359095627437497940) * 10 ^ 70 +
        7917585759906089446944146929928146273830284718525746004204560042846419) * 10 ^ 70 +
        5792957079284226229323437239210869097603201432574412372127783397189892) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 426 = 253 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 6 +
      135 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_425_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_425_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_426_prefix_zero :
    (∑ x ∈ Finset.range 254,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (426 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (426 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_426_suffix_zero :
    (∑ x ∈ Finset.range 136,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (426 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_426 :
    recurrence5Scalar1Left.coeff 426 =
      ((((107386294523803857066475433098720296028867269634563196733271875 * 10 ^ 70 +
        3610370252362912555400888746935147394181579587566999884505236835103322) * 10 ^ 70 +
        0408789978241634390415695291319741766289810678607853240692346562282188) * 10 ^ 70 +
        7282623473346095472255801556422650539726273466934528550636071915266643) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 427 = 254 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 5 +
      136 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_426_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_426_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_427_prefix_zero :
    (∑ x ∈ Finset.range 255,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (427 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (427 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_427_suffix_zero :
    (∑ x ∈ Finset.range 137,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (427 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_427 :
    recurrence5Scalar1Left.coeff 427 =
      -((((10431677770063172853926202654191340636280484427399529184206001 * 10 ^ 70 +
        4438919214154745688853085631969933516529775926641891057127558673741932) * 10 ^ 70 +
        3170406419478799251800402989423316611154282113201712343545928709322086) * 10 ^ 70 +
        2203603743193664292139572790515583220547645678965510712048053670486550) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 428 = 255 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 4 +
      137 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_427_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_427_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_428_prefix_zero :
    (∑ x ∈ Finset.range 256,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (428 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (428 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_428_suffix_zero :
    (∑ x ∈ Finset.range 138,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (428 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_428 :
    recurrence5Scalar1Left.coeff 428 =
      ((((53736262888487502652790804044585899920705612497789976688184 * 10 ^ 70 +
        3350172553465345612958603976343955195618715885750460754434595601628302) * 10 ^ 70 +
        9666888272450611413897760829323503711012480839272386431914931749493873) * 10 ^ 70 +
        7778668489704533432777291067193934020235722760168123038212213963272064) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 429 = 256 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 3 +
      138 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_428_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_428_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_429_prefix_zero :
    (∑ x ∈ Finset.range 257,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (429 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (429 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_429_suffix_zero :
    (∑ x ∈ Finset.range 139,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (429 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_429 :
    recurrence5Scalar1Left.coeff 429 =
      ((((12810467051946486800521249737919419117535489928269800239870 * 10 ^ 70 +
        4445311587590743296170456507356295392741221728422965122773151073229940) * 10 ^ 70 +
        0031272696032172328164222934188925321613985094014064018801544016385376) * 10 ^ 70 +
        9643796339145396903279752855808132835007634493578316895134702574241875) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 430 = 257 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 2 +
      139 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_429_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_429_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_430_prefix_zero :
    (∑ x ∈ Finset.range 258,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (430 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (430 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_430_suffix_zero :
    (∑ x ∈ Finset.range 140,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (430 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_430 :
    recurrence5Scalar1Left.coeff 430 =
      -((((83516301575945776881945371092346152124591556527536780077 * 10 ^ 70 +
        8805687703473687893391302242741079953358102643662442211482369882267598) * 10 ^ 70 +
        3431815413882597025724822394466572854958297304485344393477885666705435) * 10 ^ 70 +
        9165784695001808987107493220365257994118753717659013427959211344988133) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 431 = 258 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 1 +
      140 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_430_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_430_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_431_prefix_zero :
    (∑ x ∈ Finset.range 259,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (431 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (431 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_431_suffix_zero :
    (∑ x ∈ Finset.range 141,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (431 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_431 :
    recurrence5Scalar1Left.coeff 431 =
      -((((9192571289805710939343491682444695392451289460687162882 * 10 ^ 70 +
        9356667321350032351328857691450044307980872957769923023882297055059785) * 10 ^ 70 +
        7590988779280380498063292742501269954289180314271702367839826038540651) * 10 ^ 70 +
        7947663406252821980449176857764262689229198522283639700975063142556551) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 432 = 259 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_431_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_431_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_432_prefix_zero :
    (∑ x ∈ Finset.range 260,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (432 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (432 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_432_suffix_zero :
    (∑ x ∈ Finset.range 142,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (432 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_432 :
    recurrence5Scalar1Left.coeff 432 =
      -((((85218203020268547904002425297463769809471995154514690 * 10 ^ 70 +
        7039614851356799183064649620572497825112131490543252730180476901942964) * 10 ^ 70 +
        3409921726800961361727197326091523798969774490004386726146533666399317) * 10 ^ 70 +
        0850145845946674457575208262319417447072386764081381785656178083151731) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 433 = 260 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 31 +
      142 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_432_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_432_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_433_prefix_zero :
    (∑ x ∈ Finset.range 261,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (433 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (433 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_433_suffix_zero :
    (∑ x ∈ Finset.range 143,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (433 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_433 :
    recurrence5Scalar1Left.coeff 433 =
      ((((952988345016823690641722879891754814033022546469667 * 10 ^ 70 +
        9621537944724254871396800480805755953246169725903613529781486033328544) * 10 ^ 70 +
        6040365812235624034028392200726455370548701229015423565533054941012456) * 10 ^ 70 +
        9864789434071436990698024798497801434601124701068724546321333243343105) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 434 = 261 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 30 +
      143 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_433_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_433_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_434_prefix_zero :
    (∑ x ∈ Finset.range 262,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (434 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (434 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_434_suffix_zero :
    (∑ x ∈ Finset.range 144,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (434 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_434 :
    recurrence5Scalar1Left.coeff 434 =
      ((((21634893830453262398713335788907536607673320567900 * 10 ^ 70 +
        1205240141188950975638294010778075351294518130730741166156062789334683) * 10 ^ 70 +
        7329731065912127295100494559079347736618251485809956162245593047203038) * 10 ^ 70 +
        8103693251399700649614903856189868054733363513808885912870964063750740) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 435 = 262 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 29 +
      144 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_434_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_434_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_435_prefix_zero :
    (∑ x ∈ Finset.range 263,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (435 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (435 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_435_suffix_zero :
    (∑ x ∈ Finset.range 145,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (435 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_435 :
    recurrence5Scalar1Left.coeff 435 =
      ((((128082853225528166337853495433509910150621971642 * 10 ^ 70 +
        0568617424477377032376211046088064846447332007358971949863448141821272) * 10 ^ 70 +
        2085142433012819188562682738862947155454361964142820709230695946916202) * 10 ^ 70 +
        8596106130535219213933126102108794066791491109666834944014836075578219) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 436 = 263 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 28 +
      145 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_435_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_435_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_436_prefix_zero :
    (∑ x ∈ Finset.range 264,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (436 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (436 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_436_suffix_zero :
    (∑ x ∈ Finset.range 146,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (436 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_436 :
    recurrence5Scalar1Left.coeff 436 =
      -((((36442970213334337205179059875232721605950998 * 10 ^ 70 +
        3592697197420898665596307821470827916195271327248260844286507286040808) * 10 ^ 70 +
        8265914304216937446928998214442379291780832255506288287818585293965808) * 10 ^ 70 +
        8103671143686907886857338811292057627727139371818820335482024988251360) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 437 = 264 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 27 +
      146 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_436_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_436_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_437_prefix_zero :
    (∑ x ∈ Finset.range 265,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (437 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (437 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_437_suffix_zero :
    (∑ x ∈ Finset.range 147,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (437 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_437 :
    recurrence5Scalar1Left.coeff 437 =
      -((((3663478135535507718058637023099126674814725 * 10 ^ 70 +
        3480785346583347660791359327078612044591330716714241133566026226319253) * 10 ^ 70 +
        9684932342099250607640777580096312246159857392575130019404778816765318) * 10 ^ 70 +
        1249553921465088792105896845048719461253855047386774493487755396205926) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 438 = 265 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 26 +
      147 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_437_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_437_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_438_prefix_zero :
    (∑ x ∈ Finset.range 266,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (438 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (438 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_438_suffix_zero :
    (∑ x ∈ Finset.range 148,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (438 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_438 :
    recurrence5Scalar1Left.coeff 438 =
      -((((13689506242949035035188901545819366824401 * 10 ^ 70 +
        7876765542564000887523837599054894292699433015451552827886087682253396) * 10 ^ 70 +
        4714732329918333548269611168716299604365814248896133902420331891289597) * 10 ^ 70 +
        5580324151890407939381574964307861834316272141050988235278407841116992) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 439 = 266 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 25 +
      148 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_438_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_438_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_439_prefix_zero :
    (∑ x ∈ Finset.range 267,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (439 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (439 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_439_suffix_zero :
    (∑ x ∈ Finset.range 149,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (439 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_439 :
    recurrence5Scalar1Left.coeff 439 =
      ((((7351571105066955535960071299482638764 * 10 ^ 70 +
        8373512281100359242110696220336730443810937887526599215955986291898548) * 10 ^ 70 +
        0252176004071764967467573938304419811770426260001883747875947986071354) * 10 ^ 70 +
        7077140308038096661816807325599148718850147629278565409709957860498439) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 440 = 267 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 24 +
      149 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_439_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_439_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_440_prefix_zero :
    (∑ x ∈ Finset.range 268,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (440 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (440 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_440_suffix_zero :
    (∑ x ∈ Finset.range 150,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (440 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_440 :
    recurrence5Scalar1Left.coeff 440 =
      ((((148267037959701601628768459366139437 * 10 ^ 70 +
        6749594033453861822897007405348772060008845078904559742894074884620824) * 10 ^ 70 +
        8726192828652153021493797566855905228711096669101662177466194744217188) * 10 ^ 70 +
        2985579118049975524359317923712965101404538517120805732975053172650477) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 441 = 268 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 23 +
      150 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_440_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_440_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_441_prefix_zero :
    (∑ x ∈ Finset.range 269,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (441 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (441 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_441_suffix_zero :
    (∑ x ∈ Finset.range 151,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (441 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_441 :
    recurrence5Scalar1Left.coeff 441 =
      ((((197788613546625778012996101729058 * 10 ^ 70 +
        0877441283339974146098348579701835783231358805937511727858067518489906) * 10 ^ 70 +
        9741995764201909714855626929946407647189693706937632172723239841998429) * 10 ^ 70 +
        3218984640927264262386435318183905474380328393993733638424215519782511) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 442 = 269 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 22 +
      151 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_441_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_441_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_442_prefix_zero :
    (∑ x ∈ Finset.range 270,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (442 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (442 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_442_suffix_zero :
    (∑ x ∈ Finset.range 152,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (442 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_442 :
    recurrence5Scalar1Left.coeff 442 =
      -((((564541713319324239836907779990 * 10 ^ 70 +
        8665154220406415872640663933212589595155163150773405713720721429669836) * 10 ^ 70 +
        2967252689233461938512587935582550930346300727470924919262660627909699) * 10 ^ 70 +
        9965560268518310558058036670156635878785544116443049955188322606673213) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 443 = 270 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 21 +
      152 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_442_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_442_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_443_prefix_zero :
    (∑ x ∈ Finset.range 271,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (443 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (443 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_443_suffix_zero :
    (∑ x ∈ Finset.range 153,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (443 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_443 :
    recurrence5Scalar1Left.coeff 443 =
      -((((1370814416433161395945490534 * 10 ^ 70 +
        6205700943453983017171697561830872177712788351433183935047570448869328) * 10 ^ 70 +
        7078455353565476853399381972216892776451509147758003751078257538482785) * 10 ^ 70 +
        3401428387129823006668546494119742654678403425950257275549963508504860) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 444 = 271 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 20 +
      153 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_443_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_443_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_444_prefix_zero :
    (∑ x ∈ Finset.range 272,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (444 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (444 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_444_suffix_zero :
    (∑ x ∈ Finset.range 154,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (444 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_444 :
    recurrence5Scalar1Left.coeff 444 =
      ((((751867220364127877369758 * 10 ^ 70 +
        1314756283673832007030254357362948250077587462413034697569565516975453) * 10 ^ 70 +
        9180396562867515054973034921110281982868199148950672600695188328207759) * 10 ^ 70 +
        8237422276441132822628553139747016405701511046483423538482727568089676) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 445 = 272 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 19 +
      154 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_444_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_444_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_445_prefix_zero :
    (∑ x ∈ Finset.range 273,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (445 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (445 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_445_suffix_zero :
    (∑ x ∈ Finset.range 155,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (445 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_445 :
    recurrence5Scalar1Left.coeff 445 =
      ((((3423459101124961910208 * 10 ^ 70 +
        5559560409248255790238795953599699163526287493918302735792486903962430) * 10 ^ 70 +
        8267737891469077113617512578821908203708877850133592896003349132522888) * 10 ^ 70 +
        4781353862115480001283123044626044017456734015643789725755042890117535) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 446 = 273 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 18 +
      155 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_445_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_445_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_446_prefix_zero :
    (∑ x ∈ Finset.range 274,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (446 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (446 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_446_suffix_zero :
    (∑ x ∈ Finset.range 156,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (446 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_446 :
    recurrence5Scalar1Left.coeff 446 =
      ((((203563870931075676 * 10 ^ 70 +
        3548100409269076923637613405345333597191814938434062762000166582555793) * 10 ^ 70 +
        7697821872397677813381038649868583373781655892444617762782269028469155) * 10 ^ 70 +
        4520503581597226829943273849891395976189432081053974810860676656624825) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 447 = 274 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 17 +
      156 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_446_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_446_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_447_prefix_zero :
    (∑ x ∈ Finset.range 275,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (447 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (447 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_447_suffix_zero :
    (∑ x ∈ Finset.range 157,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (447 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_447 :
    recurrence5Scalar1Left.coeff 447 =
      -((((3173981053614377 * 10 ^ 70 +
        8034115566451110649352661448991193037034134301924414861268113658453629) * 10 ^ 70 +
        7170861835787916398633375694175504284286263051144486011350590937629774) * 10 ^ 70 +
        8799718562109781474070863663739815758573831847928084713468038870585745) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 448 = 275 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 16 +
      157 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_447_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_447_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_448_prefix_zero :
    (∑ x ∈ Finset.range 276,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (448 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (448 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_448_suffix_zero :
    (∑ x ∈ Finset.range 158,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (448 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_448 :
    recurrence5Scalar1Left.coeff 448 =
      -((((1054422241002 * 10 ^ 70 +
        9501243920107550071815745955375946780685406829791114245835580548392750) * 10 ^ 70 +
        3021500356619812844630297644073547810340870886001699026619858944488142) * 10 ^ 70 +
        4256878163045838653076272245685111520505982549673464962985167257469444) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 449 = 276 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 15 +
      158 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_448_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_448_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_449_prefix_zero :
    (∑ x ∈ Finset.range 277,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (449 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (449 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_449_suffix_zero :
    (∑ x ∈ Finset.range 159,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (449 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_449 :
    recurrence5Scalar1Left.coeff 449 =
      ((((587470288 * 10 ^ 70 +
        3519800468979933573891692645731652664617920657666831055917062405653376) * 10 ^ 70 +
        7027468824752268482497998553459920709014478454541418101684222060056719) * 10 ^ 70 +
        2847004718375564220908202365671009355123963543886900364866775032483065) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 450 = 277 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 14 +
      159 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_449_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_449_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_450_prefix_zero :
    (∑ x ∈ Finset.range 278,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (450 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (450 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_450_suffix_zero :
    (∑ x ∈ Finset.range 160,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (450 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_450 :
    recurrence5Scalar1Left.coeff 450 =
      ((((174494 * 10 ^ 70 +
        4832374577114086814545187319468637274352931439275813376045760957939200) * 10 ^ 70 +
        1661703860563443479778587543651810609861752552209171856583033645993996) * 10 ^ 70 +
        7144926172349252929299124559255820206849646240801719656790301076652124) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 451 = 278 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 13 +
      160 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_450_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_450_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_451_prefix_zero :
    (∑ x ∈ Finset.range 279,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (451 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (451 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_451_suffix_zero :
    (∑ x ∈ Finset.range 161,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (451 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_451 :
    recurrence5Scalar1Left.coeff 451 =
      -((((2 * 10 ^ 70 +
        4501079939093971340675039580401489671100506872527000003553320752984822) * 10 ^ 70 +
        8436171998428294540036228298734808007461901087968912688985400271322261) * 10 ^ 70 +
        8960164394906591764856504782918427470058652111276134277945935365088923) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 452 = 279 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 12 +
      161 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_451_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_451_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_452_prefix_zero :
    (∑ x ∈ Finset.range 280,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (452 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (452 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_452_suffix_zero :
    (∑ x ∈ Finset.range 162,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (452 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_452 :
    recurrence5Scalar1Left.coeff 452 =
      -(((24905541595478205183851461884628049791687245511417642350013501449910 * 10 ^ 70 +
        6911862056583879754031667544464742003692812661279934953133072792835094) * 10 ^ 70 +
        8185788781588282429019351312254345783138092443216230493683643888400714) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 453 = 280 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 11 +
      162 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_452_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_452_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_453_prefix_zero :
    (∑ x ∈ Finset.range 281,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (453 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (453 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_453_suffix_zero :
    (∑ x ∈ Finset.range 163,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (453 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_453 :
    recurrence5Scalar1Left.coeff 453 =
      -(((524569885274956075538517580362231907080621738942785366729622065 * 10 ^ 70 +
        1073168177455392702952330424837551774700907155136266012828908627517890) * 10 ^ 70 +
        5427865462710230355676309974435951861761114786988709007814524262522878) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 454 = 281 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 10 +
      163 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_453_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_453_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_454_prefix_zero :
    (∑ x ∈ Finset.range 282,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (454 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (454 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_454_suffix_zero :
    (∑ x ∈ Finset.range 164,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (454 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_454 :
    recurrence5Scalar1Left.coeff 454 =
      (((15487915382002670165333236294047144179608432934301462923984 * 10 ^ 70 +
        5616859827122641853030317821621643123886729136043167425068041484914119) * 10 ^ 70 +
        4196316190582417614767240371440752968509437505323375299337231645457716) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 455 = 282 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 9 +
      164 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_454_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_454_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_455_prefix_zero :
    (∑ x ∈ Finset.range 283,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (455 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (455 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_455_suffix_zero :
    (∑ x ∈ Finset.range 165,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (455 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_455 :
    recurrence5Scalar1Left.coeff 455 =
      (((348626838348247559701127899010880677546518861440188414 * 10 ^ 70 +
        3610817757909162491983950176334466743611018320909302536907746195797566) * 10 ^ 70 +
        0803368662494149057838019409221111486900896106238389814033985029802470) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 456 = 283 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 8 +
      165 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_455_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_455_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_456_prefix_zero :
    (∑ x ∈ Finset.range 284,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (456 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (456 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_456_suffix_zero :
    (∑ x ∈ Finset.range 166,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (456 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_456 :
    recurrence5Scalar1Left.coeff 456 =
      -(((217522143824704195917331552518764075321547454747 * 10 ^ 70 +
        1728615348067739103709051611524312963842317968708641810269752290309214) * 10 ^ 70 +
        3622431118282219736725246361112303234699502655676597606840299795715024) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 457 = 284 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 7 +
      166 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_456_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_456_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_457_prefix_zero :
    (∑ x ∈ Finset.range 285,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (457 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (457 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_457_suffix_zero :
    (∑ x ∈ Finset.range 167,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (457 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_457 :
    recurrence5Scalar1Left.coeff 457 =
      -(((4064839417357928529057645881947575322794350 * 10 ^ 70 +
        4114718389639758785933847087096381017482857776827214959374689755135132) * 10 ^ 70 +
        0968502197674664306128048425047649784347903497314763328734089646292870) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 458 = 285 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 6 +
      167 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_457_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_457_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_458_prefix_zero :
    (∑ x ∈ Finset.range 286,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (458 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (458 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_458_suffix_zero :
    (∑ x ∈ Finset.range 168,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (458 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_458 :
    recurrence5Scalar1Left.coeff 458 =
      -(((4206695916775164961007061209694576086 * 10 ^ 70 +
        7679760664403190454921122952004535726488713649618641908621661532880586) * 10 ^ 70 +
        1226040203552907406011585823517525472056652749000958978258437238203178) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 459 = 286 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 5 +
      168 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_458_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_458_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_459_prefix_zero :
    (∑ x ∈ Finset.range 287,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (459 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (459 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_459_suffix_zero :
    (∑ x ∈ Finset.range 169,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (459 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_459 :
    recurrence5Scalar1Left.coeff 459 =
      (((1169811484490736439374355220411 * 10 ^ 70 +
        9026395409341168684878506730797168629760188128842492333713651177318892) * 10 ^ 70 +
        5893711170417303243909853034933025355724652756067713360994917403343963) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 460 = 287 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 4 +
      169 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_459_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_459_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_460_prefix_zero :
    (∑ x ∈ Finset.range 288,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (460 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (460 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_460_suffix_zero :
    (∑ x ∈ Finset.range 170,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (460 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_460 :
    recurrence5Scalar1Left.coeff 460 =
      (((212205151593338073966312 * 10 ^ 70 +
        2293610272081520982496614430939755329216320309398098065236544710644624) * 10 ^ 70 +
        4568907116498860726427595008168396061365812679303747101045808906790973) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 461 = 288 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 3 +
      170 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_460_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_460_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_461_prefix_zero :
    (∑ x ∈ Finset.range 289,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (461 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (461 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_461_suffix_zero :
    (∑ x ∈ Finset.range 171,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (461 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_461 :
    recurrence5Scalar1Left.coeff 461 =
      (((6527768120902001 * 10 ^ 70 +
        5563575994183027261417333016853684974191645622711791191878824573934833) * 10 ^ 70 +
        3322652562278513778234011964417701517470104574165549532899066455133736) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 462 = 289 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 2 +
      171 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_461_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_461_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_462_prefix_zero :
    (∑ x ∈ Finset.range 290,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (462 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (462 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_462_suffix_zero :
    (∑ x ∈ Finset.range 172,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (462 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_462 :
    recurrence5Scalar1Left.coeff 462 =
      -(((88239415 * 10 ^ 70 +
        1525819178809293958690451432043294141122951017995138852984640509550220) * 10 ^ 70 +
        5648204259801058859189596893598983474662405357202388878875943562866609) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 463 = 290 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 1 +
      172 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_462_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_462_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
