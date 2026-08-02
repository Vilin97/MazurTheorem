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

private theorem recurrence5Scalar1Left_coeff_223_prefix_zero :
    (∑ x ∈ Finset.range 51,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (223 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (223 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_223 :
    recurrence5Scalar1Left.coeff 223 =
      ((((((1860585187 * 10 ^ 70 +
        0342332391129008310043692033449558196580868621243330058611515990386578) * 10 ^ 70 +
        7308661497626345617239471959250511700170875311311283257781703041350755) * 10 ^ 70 +
        0282113430976370274787658483241317120351175415181099818686628059925050) * 10 ^ 70 +
        8755144045107492185940123217979753004704893099484979522255313892636553) * 10 ^ 70 +
        1809924837369920547237426705925087835464954613548954578066989797657475) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 224 = 51 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_223_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_224_prefix_zero :
    (∑ x ∈ Finset.range 52,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (224 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (224 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_224 :
    recurrence5Scalar1Left.coeff 224 =
      -((((((1209824727 * 10 ^ 70 +
        9290647654255508805640474632279948586106341629796528955053481505183161) * 10 ^ 70 +
        9789612045045402262544092228712402311518266931464916227955937996772464) * 10 ^ 70 +
        9324735660618785855665299272987510938886706302315812285380794810756781) * 10 ^ 70 +
        8982153589545412623119582869748839977989590202176752820559013861327097) * 10 ^ 70 +
        7608705547900384061010120679506040763225674170555261929800054888205237) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 225 = 52 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_224_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_225_prefix_zero :
    (∑ x ∈ Finset.range 53,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (225 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (225 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_225 :
    recurrence5Scalar1Left.coeff 225 =
      ((((((722310108 * 10 ^ 70 +
        5154196137272127133174461783548872829171245001168623829104732630827931) * 10 ^ 70 +
        1621989251360469151398428044594972318990889252862358844501038612405087) * 10 ^ 70 +
        2679379882930263295469121588777154132235081956464283734073528582504642) * 10 ^ 70 +
        1065198373111978986276314860670246584980170660810959356182347635547203) * 10 ^ 70 +
        4934379106554372561283448383563252985247693975675666132300832212618116) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 226 = 53 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_225_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_226_prefix_zero :
    (∑ x ∈ Finset.range 54,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (226 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (226 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_226 :
    recurrence5Scalar1Left.coeff 226 =
      -((((((372981467 * 10 ^ 70 +
        0492966629942895304582997871453172959311661784381004166647904117448534) * 10 ^ 70 +
        7341287549945642185423390435432616168374661348495016334893727252536422) * 10 ^ 70 +
        7028313405133334164893843406631107812642572448354891515217466239984973) * 10 ^ 70 +
        6442842004113142623521596485766567538668475221310460663975022591101516) * 10 ^ 70 +
        2637382567102829058319698446062306912527442135550026175659246422614893) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 227 = 54 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_226_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_227_prefix_zero :
    (∑ x ∈ Finset.range 55,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (227 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (227 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_227 :
    recurrence5Scalar1Left.coeff 227 =
      ((((((135893124 * 10 ^ 70 +
        3833838989505630022947470273801747362547740886832728610495032880942656) * 10 ^ 70 +
        2825625117521891737141575520508931177424987280625527101182763515800898) * 10 ^ 70 +
        6099549334829387159227240877256797612411908737453012062509683683256170) * 10 ^ 70 +
        1393552312345032227989102785672134460511222635965291194351570769960869) * 10 ^ 70 +
        1537178670811196079839177923759650063183681309145544483428350882898695) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 228 = 55 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_227_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_228_prefix_zero :
    (∑ x ∈ Finset.range 56,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (228 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (228 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_228 :
    recurrence5Scalar1Left.coeff 228 =
      ((((((13841044 * 10 ^ 70 +
        5973953096263042938091728717259861282489962796145858576040264549380286) * 10 ^ 70 +
        1916860165066245243561765649641633962130761349736054617577612884194357) * 10 ^ 70 +
        7097497689449270486468502018149852521401549694629159277907788872388232) * 10 ^ 70 +
        0006575426602184096337983539369578395392218098268027695005834418469259) * 10 ^ 70 +
        6471175411516263001967326293736507285364638726638974825933521635544007) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 229 = 56 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_228_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_229_prefix_zero :
    (∑ x ∈ Finset.range 57,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (229 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (229 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_229 :
    recurrence5Scalar1Left.coeff 229 =
      -((((((98665273 * 10 ^ 70 +
        1651835761263560185080538645158066103436624359102842887154037390284056) * 10 ^ 70 +
        8368463311201699928648315350618900682988794394686010491462357381607795) * 10 ^ 70 +
        5639717946318164315872984624425390461825596602294672849510818117145984) * 10 ^ 70 +
        8106541956529652968806883916001988681285392875730995522463270888561832) * 10 ^ 70 +
        7454555428942176628421399678510854470389071034017091672981265543882024) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 230 = 57 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_229_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_230_prefix_zero :
    (∑ x ∈ Finset.range 58,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (230 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (230 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_230 :
    recurrence5Scalar1Left.coeff 230 =
      ((((((137753250 * 10 ^ 70 +
        7735283370358813123718516054467960720686174076531437404867220545424670) * 10 ^ 70 +
        4872468448457627613042416442117242364450197159847737703773076184432889) * 10 ^ 70 +
        0544743897362860683567345601687418084768223427111747541157134588762323) * 10 ^ 70 +
        6619979623767891648583501364195403149247280866652453965555636295478911) * 10 ^ 70 +
        4988553677216146967002806635562290460263532658201965524020751247817373) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 231 = 58 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_230_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_231_prefix_zero :
    (∑ x ∈ Finset.range 59,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (231 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (231 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_231 :
    recurrence5Scalar1Left.coeff 231 =
      -((((((146667111 * 10 ^ 70 +
        8070510777000129186857869732722534281528553056029687296393891363337332) * 10 ^ 70 +
        9831001095773760979042061065489662130458447199138323591999881555386224) * 10 ^ 70 +
        7617241364755276543052407129228110429689425435830980149509115281475470) * 10 ^ 70 +
        7076673086675303697612836088519985470464336048367541537169941526329936) * 10 ^ 70 +
        0823295325209575141036181524457564039336834744107577506894548186828117) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 232 = 59 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_231_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_232_prefix_zero :
    (∑ x ∈ Finset.range 60,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (232 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (232 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_232 :
    recurrence5Scalar1Left.coeff 232 =
      ((((((137403507 * 10 ^ 70 +
        8744478831891398840812317919659919005575380011429000722338223658718017) * 10 ^ 70 +
        7209558250997445491647204720251252447516786708235698067053784853642307) * 10 ^ 70 +
        5216714506633667939670209958975031664592778374207211087135704783381014) * 10 ^ 70 +
        6266201641692545469808809432887722793398801808379440971459668693828011) * 10 ^ 70 +
        7376967094983303353070794542441426883715292243333321057951060716012391) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 233 = 60 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_232_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_233_prefix_zero :
    (∑ x ∈ Finset.range 61,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (233 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (233 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_233 :
    recurrence5Scalar1Left.coeff 233 =
      -((((((118712738 * 10 ^ 70 +
        4250659464071944777234953310230291511802913186096557524812738172120246) * 10 ^ 70 +
        5105765072830092152433425683188363863188512369179433794100549096455508) * 10 ^ 70 +
        4671838585915120045831907840041084903177643559095418290145553168711891) * 10 ^ 70 +
        2441906399305134615515155166105335417978724391650988729803576990019897) * 10 ^ 70 +
        2462444606335308826504755057565053202489448755753874726174871139659741) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 234 = 61 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_233_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_234_prefix_zero :
    (∑ x ∈ Finset.range 62,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (234 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (234 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_234 :
    recurrence5Scalar1Left.coeff 234 =
      ((((((96580609 * 10 ^ 70 +
        3534634074458419662865151173980677019473716086025310382836551109342449) * 10 ^ 70 +
        0373465633107958844313160333929495983414816441800978850333152060919050) * 10 ^ 70 +
        3654588385115392341494509299989862873013862019951895154669508306511252) * 10 ^ 70 +
        2624370936404896684224532109568516997356947982060877166151689385936245) * 10 ^ 70 +
        6499287775898318405137040523769141584082452884496894988788028363107921) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 235 = 62 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_234_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_235_prefix_zero :
    (∑ x ∈ Finset.range 63,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (235 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (235 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_235 :
    recurrence5Scalar1Left.coeff 235 =
      -((((((74778267 * 10 ^ 70 +
        1791530268982016497072648058988338595809484592204169730016421699323643) * 10 ^ 70 +
        4769805028304001718608169364870387075968924595724221169361003379485813) * 10 ^ 70 +
        0408157489478233290546192802378729133204136428855657233600494861100598) * 10 ^ 70 +
        8807356506965763303071714282836344724564168347846356475173023168138192) * 10 ^ 70 +
        9514098157018057721016995725708519258738333305417091785430255983237092) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 236 = 63 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_235_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_236_prefix_zero :
    (∑ x ∈ Finset.range 64,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (236 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (236 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_236 :
    recurrence5Scalar1Left.coeff 236 =
      ((((((55407249 * 10 ^ 70 +
        9321980847536963893580744878854658710644536943410623207310594017232557) * 10 ^ 70 +
        5527925011649127770081335324326749727189312201754840847563674147231659) * 10 ^ 70 +
        5420797510221303744056438483169463102032570191854415210520772377010745) * 10 ^ 70 +
        3407453458712520255756892302326176291994333270147672743705114006839551) * 10 ^ 70 +
        3035762031225959349043190370493207392179681735027754966828969438976977) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 237 = 64 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_236_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_237_prefix_zero :
    (∑ x ∈ Finset.range 65,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (237 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (237 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_237 :
    recurrence5Scalar1Left.coeff 237 =
      -((((((39390647 * 10 ^ 70 +
        7315822078251438685254963125466015939735081044121823241841804558522250) * 10 ^ 70 +
        4165969819195211427813612492054272402216452897224950700539997396433974) * 10 ^ 70 +
        4020311198259034233487158052481072546789103926571179791839077634908828) * 10 ^ 70 +
        3903372577625693304029859110349740164933498932559404969636762022552711) * 10 ^ 70 +
        9428193625841354136150693844955771048026143867557723111693527580451983) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 238 = 65 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_237_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_238_prefix_zero :
    (∑ x ∈ Finset.range 66,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (238 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (238 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_238 :
    recurrence5Scalar1Left.coeff 238 =
      ((((((26883042 * 10 ^ 70 +
        7265468102272791527553417860833299443809308016532055745914350487344546) * 10 ^ 70 +
        0486665627911414508562212331997814087289083256375562473718555995911280) * 10 ^ 70 +
        9593759470710006661511460484951459822510326042573074850497829215191454) * 10 ^ 70 +
        7452172911107312806676048885422503653895962471666539994794022673866711) * 10 ^ 70 +
        4685570311831482684613465026984048897648606689848379418614709794553094) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 239 = 66 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_238_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_239_prefix_zero :
    (∑ x ∈ Finset.range 67,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (239 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (239 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_239 :
    recurrence5Scalar1Left.coeff 239 =
      -((((((17589644 * 10 ^ 70 +
        1837866095155664016879486478303853686024586149380812826827402655310026) * 10 ^ 70 +
        9695441744353252682090369817711213109086327176128400325471342090991065) * 10 ^ 70 +
        6847394102226726803129656039438928614160510116016802396683943848629060) * 10 ^ 70 +
        2720231203287562573173528380138588207429670283667546040910441241116157) * 10 ^ 70 +
        2807768696802870578394306568623942694259175033296858653406464114816975) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 240 = 67 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_239_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_240_prefix_zero :
    (∑ x ∈ Finset.range 68,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (240 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (240 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_240 :
    recurrence5Scalar1Left.coeff 240 =
      ((((((10997853 * 10 ^ 70 +
        0434197221779149928087860002624448972128765896212450798185231699702117) * 10 ^ 70 +
        2754806096653367761437444754821025544813737783097993119527634329999169) * 10 ^ 70 +
        2884252576912422671078134635522801460521671576339727047076070293611787) * 10 ^ 70 +
        6854085963621748393984397325432724769281040726184534584997478514632211) * 10 ^ 70 +
        3827732330390706876683408560326121755835178312387256986337579305408351) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 241 = 68 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_240_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_241_prefix_zero :
    (∑ x ∈ Finset.range 69,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (241 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (241 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_241 :
    recurrence5Scalar1Left.coeff 241 =
      -((((((6532458 * 10 ^ 70 +
        8334174612851507609118388366721087817752817000091068343295548773822235) * 10 ^ 70 +
        0386974934546873567762161104462133139560030972572159644943488872507284) * 10 ^ 70 +
        0781956378328647378915134924800085259031739606932391223291780156256431) * 10 ^ 70 +
        7068107153907130272791300162054172414445361692103743331387244243381412) * 10 ^ 70 +
        4231982686742712999066559412758353795845170606686448592383831423703840) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 242 = 69 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_241_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_242_prefix_zero :
    (∑ x ∈ Finset.range 70,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (242 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (242 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_242 :
    recurrence5Scalar1Left.coeff 242 =
      ((((((3649498 * 10 ^ 70 +
        8578314346916900753576168774483038599120581333323467170692979641033014) * 10 ^ 70 +
        1828024852621146448210143622970100034486213995707827650244213408704119) * 10 ^ 70 +
        4872483360912336428404161366780276881899654919498958003035291817501726) * 10 ^ 70 +
        3937403979502168334199013859213523408661402825619086016911852072988019) * 10 ^ 70 +
        9729107754577099799485132776426372507875477208076659456604292453967245) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 243 = 70 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_242_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_243_prefix_zero :
    (∑ x ∈ Finset.range 71,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (243 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (243 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_243 :
    recurrence5Scalar1Left.coeff 243 =
      -((((((1884510 * 10 ^ 70 +
        1534740380653817319048711331215241811946799460160940444885091675418905) * 10 ^ 70 +
        9956751753790387965893862390081556336087801508660102996579386561208357) * 10 ^ 70 +
        8966066308617807302958695470395046199024686808110749634579977221120113) * 10 ^ 70 +
        6988798479081969030769282739997261505347248516445825884133884046245259) * 10 ^ 70 +
        2893093406023453554264184521322063485992816482098475888853201837389881) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 244 = 71 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_243_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_244_prefix_zero :
    (∑ x ∈ Finset.range 72,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (244 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (244 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_244 :
    recurrence5Scalar1Left.coeff 244 =
      ((((((869543 * 10 ^ 70 +
        9434865929775382527256295511847863003769383793976327598120262991609723) * 10 ^ 70 +
        5307665667812363699112135428850219875221312719373420712292268966839790) * 10 ^ 70 +
        0428632355531963117461203179971080693618204150514094810321348209772680) * 10 ^ 70 +
        9164988296346009414796856135454731493965471251964350100777687250703858) * 10 ^ 70 +
        7499202719961221677767429060683370646098517924243917831697593900821898) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 245 = 72 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_244_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_245_prefix_zero :
    (∑ x ∈ Finset.range 73,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (245 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (245 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_245 :
    recurrence5Scalar1Left.coeff 245 =
      -((((((330834 * 10 ^ 70 +
        5056335054166283372022433225897178560710623430761230656920303899059780) * 10 ^ 70 +
        8413390691294421137173506019974251071675849574535767314154448404557809) * 10 ^ 70 +
        9739663955033662118269253050473117366248941329193758866325296685665738) * 10 ^ 70 +
        4711058241613987280344740991526075143862684636440439541567986480713567) * 10 ^ 70 +
        8362087435706755650975042929109444142345369849072824362623692240538009) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 246 = 73 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_245_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_246_prefix_zero :
    (∑ x ∈ Finset.range 74,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (246 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (246 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_246 :
    recurrence5Scalar1Left.coeff 246 =
      ((((((76154 * 10 ^ 70 +
        2796479183493416223025298333401117291193039607843278215071174552675553) * 10 ^ 70 +
        0495295842229913672363993121278522214112836548510994104327252185837150) * 10 ^ 70 +
        6089548804227118921304864510641304896460163884672746388782415787805823) * 10 ^ 70 +
        9137041327618968287202007978802478057613163347435091039167413333899171) * 10 ^ 70 +
        6858973680948108589309256747141105969909198445829990752865682595381068) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 247 = 74 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_246_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_247_prefix_zero :
    (∑ x ∈ Finset.range 75,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (247 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (247 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_247 :
    recurrence5Scalar1Left.coeff 247 =
      ((((((21853 * 10 ^ 70 +
        5431009058858140348742894698356069658340647167520021047323549600078386) * 10 ^ 70 +
        2384048517628561380847940807916234900815885143286073230452090239366802) * 10 ^ 70 +
        4811727942011078391486977790505546750906611538552391145313844405400371) * 10 ^ 70 +
        2065824786204143906266987334550067429342187495701835059383307978874559) * 10 ^ 70 +
        6426477485007330830618418640183289200828792009982728926602003344518916) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 248 = 75 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_247_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_248_prefix_zero :
    (∑ x ∈ Finset.range 76,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (248 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (248 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_248 :
    recurrence5Scalar1Left.coeff 248 =
      -((((((42405 * 10 ^ 70 +
        5767076400338928441408522102540395547295731066943246286635104025302156) * 10 ^ 70 +
        5183432219395987037798558360120426783592761487762891390943273088333165) * 10 ^ 70 +
        2606150263778460266553045090716070629216616757097077779453896783474630) * 10 ^ 70 +
        7759515826785188899954536148836824221854840462171773539267633990107224) * 10 ^ 70 +
        3623060407003702661360507696918701166831250643074661934693443049093456) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 249 = 76 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_248_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_249_prefix_zero :
    (∑ x ∈ Finset.range 77,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (249 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (249 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_249 :
    recurrence5Scalar1Left.coeff 249 =
      ((((((31215 * 10 ^ 70 +
        4124088584009475424155892639279375621832378031240834475689663835937157) * 10 ^ 70 +
        0514040304895053471992481197972122547668774657354719177886302329176465) * 10 ^ 70 +
        9411744993215053051196663369391281287888740606242938456061312210735175) * 10 ^ 70 +
        2543511801662833411394746388928172201569683487474191181699906597641851) * 10 ^ 70 +
        0557566659077153386069546427319703015516984546741948783116900578622893) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 250 = 77 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_249_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_250_prefix_zero :
    (∑ x ∈ Finset.range 78,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (250 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (250 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_250 :
    recurrence5Scalar1Left.coeff 250 =
      -((((((12152 * 10 ^ 70 +
        2430710040050828476331274437591972048248832573365032311581394406706154) * 10 ^ 70 +
        3437413161646034988774341510811358698220850669177331514366943191271359) * 10 ^ 70 +
        4589041930507917992025122810493200460457376962445897173080022177235085) * 10 ^ 70 +
        9402684421019691697955923487279915741815871622952534397328900996835571) * 10 ^ 70 +
        6141819269700185478968853458882645527331762074521987104598871976462867) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 251 = 78 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_250_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_251_prefix_zero :
    (∑ x ∈ Finset.range 79,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (251 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (251 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_251 :
    recurrence5Scalar1Left.coeff 251 =
      -((((((4156 * 10 ^ 70 +
        3650990071803024719086942408998992953348969639833626207503607761612225) * 10 ^ 70 +
        0439810616401341252266771717461153682508797751864110971066347818013474) * 10 ^ 70 +
        3832909625737823114988966557916088952817185662571416202713889752435474) * 10 ^ 70 +
        6022704477346260468736410009059483069526601772770417638849260117457760) * 10 ^ 70 +
        2921176082910365870359896671072778091292366271391137774497836367170421) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 252 = 79 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_251_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_252_prefix_zero :
    (∑ x ∈ Finset.range 80,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (252 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (252 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_252 :
    recurrence5Scalar1Left.coeff 252 =
      ((((((14410 * 10 ^ 70 +
        4362318050510494699854880567076091944704719533476536354892581992644891) * 10 ^ 70 +
        2435137782895953045938963041406295781505026242251886329140040897095964) * 10 ^ 70 +
        1889885141821902586325470895978748000488740395571917411179428180029159) * 10 ^ 70 +
        8691154444197201909518505522176507951879180622681845380433437495147624) * 10 ^ 70 +
        8753154825576208215741760712468406791449769772759609879163220514183792) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 253 = 80 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_252_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_253_prefix_zero :
    (∑ x ∈ Finset.range 81,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (253 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (253 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_253 :
    recurrence5Scalar1Left.coeff 253 =
      -((((((18859 * 10 ^ 70 +
        0700288199072014200517648538765771935773493353097284092976153764145397) * 10 ^ 70 +
        7163927019705567878400554370615246848856188828494132248667657454354901) * 10 ^ 70 +
        6072522845608516977000338038902078439374072993625508140222675405515926) * 10 ^ 70 +
        9561261272775830112081126635429945254858750908575398752738563450458533) * 10 ^ 70 +
        8781941517007865723792973127522960024294188593483028168014910708439518) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 254 = 81 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_253_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_254_prefix_zero :
    (∑ x ∈ Finset.range 82,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (254 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (254 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_254 :
    recurrence5Scalar1Left.coeff 254 =
      ((((((19082 * 10 ^ 70 +
        8779634042941004954006134823240141980535663947427526431416199181228285) * 10 ^ 70 +
        7973165008021742878409001046321896841038844597469532335146235267764335) * 10 ^ 70 +
        4732335270135327004507781678266578955655739204038366076134569232976009) * 10 ^ 70 +
        0136269870780161749277100337124476918827961545043482718136324059193979) * 10 ^ 70 +
        2295908135008301247080735802710006627368526130211494949478987307409358) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 255 = 82 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_254_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_255_prefix_zero :
    (∑ x ∈ Finset.range 83,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (255 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (255 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_255 :
    recurrence5Scalar1Left.coeff 255 =
      -((((((16832 * 10 ^ 70 +
        0663249640578951870641593837387600171308181619337693530521804828082596) * 10 ^ 70 +
        0512541472979003107343844827470221913803289469637351615841574218936432) * 10 ^ 70 +
        0381956652063040893667853332349815155087650163005955837703630896145294) * 10 ^ 70 +
        0120043321980918205738273675768911930254759373235734136779049574487924) * 10 ^ 70 +
        9711012247153413553637062576432042603949391986392053665596972724538178) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 256 = 83 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_255_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_256_prefix_zero :
    (∑ x ∈ Finset.range 84,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (256 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (256 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_256 :
    recurrence5Scalar1Left.coeff 256 =
      ((((((13521 * 10 ^ 70 +
        8978202697282720332239122407974057157340880012984914213655717251789382) * 10 ^ 70 +
        3726984669721263071932919231184361192119135584020365498778621116993097) * 10 ^ 70 +
        5196222901180687116385331468266730569049121553293034324438954841110300) * 10 ^ 70 +
        4184718608169166587562533592509636343396435482029892298969750500699987) * 10 ^ 70 +
        0471985108387952444067369660662133936359813444552422325810481069125398) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 257 = 84 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_256_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_257_prefix_zero :
    (∑ x ∈ Finset.range 85,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (257 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (257 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_257 :
    recurrence5Scalar1Left.coeff 257 =
      -((((((10098 * 10 ^ 70 +
        4497397281666817465853824793846604055332915247080729709263319012001806) * 10 ^ 70 +
        8542029289363885398186306940986292126220149094859331754364079121977277) * 10 ^ 70 +
        7081860276602073556750187470441683622669612058718863729402670636380924) * 10 ^ 70 +
        5726784584542053722515473296223618219938018765121753931125410633008991) * 10 ^ 70 +
        2468134548532005814521182430136637791357800702538713803160559774500205) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 258 = 85 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_257_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_258_prefix_zero :
    (∑ x ∈ Finset.range 86,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (258 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (258 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_258 :
    recurrence5Scalar1Left.coeff 258 =
      ((((((7084 * 10 ^ 70 +
        6188370185012701396148531168401292650817744736978951796713988223042968) * 10 ^ 70 +
        7535356041077916668414318003963081399015524867650120861832661875043111) * 10 ^ 70 +
        5103751807468132633469581053612786142735446798448350220239928682239096) * 10 ^ 70 +
        6984204369749850053767013562640601804184145430232956451120598130642886) * 10 ^ 70 +
        2340995480576240795968263114880289957395936421936866413369623284561771) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 259 = 86 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_258_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_259_prefix_zero :
    (∑ x ∈ Finset.range 87,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (259 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (259 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_259 :
    recurrence5Scalar1Left.coeff 259 =
      -((((((4691 * 10 ^ 70 +
        7946675560556133913315810553817640843585360085186871558638320283054149) * 10 ^ 70 +
        8428831297922783820181055889272920222348018109484802773992445394761794) * 10 ^ 70 +
        7843455040075677308928791115865744516851958468878302963589371258279541) * 10 ^ 70 +
        9297581229593525739096648745217323414305089702659193730702288683897813) * 10 ^ 70 +
        7587274618139760088876463999976368037455512848109707319345461317580480) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 260 = 87 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_259_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_260_prefix_zero :
    (∑ x ∈ Finset.range 88,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (260 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (260 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_260 :
    recurrence5Scalar1Left.coeff 260 =
      ((((((2935 * 10 ^ 70 +
        9921999647933826354907794566972794715284158537833252416931475067972845) * 10 ^ 70 +
        0290918926792004491636705524065330159001245467976353651711547728324001) * 10 ^ 70 +
        8505890039371399513660238685053282561975411092743867561739979738211137) * 10 ^ 70 +
        7507509966658124844008481141278518018927430371734783764483303310430834) * 10 ^ 70 +
        2349421350647132161083395616275587748105447904267197621791711105297796) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 261 = 88 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_260_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_261_prefix_zero :
    (∑ x ∈ Finset.range 89,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (261 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (261 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_261 :
    recurrence5Scalar1Left.coeff 261 =
      -((((((1731 * 10 ^ 70 +
        6139123067061722030390744126195623523883104498077397486243581304002602) * 10 ^ 70 +
        2743650957984466400463326637900892309177291212909085215292081717147920) * 10 ^ 70 +
        7360177543779976329209421457080514370793000336904482451102060298338477) * 10 ^ 70 +
        1742506517214926885755464425156366148956671738131239068656211835724497) * 10 ^ 70 +
        1393586025949413346985081753480253913684119568039986174751225049282968) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 262 = 89 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_261_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_262_prefix_zero :
    (∑ x ∈ Finset.range 90,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (262 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (262 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_262 :
    recurrence5Scalar1Left.coeff 262 =
      ((((((955 * 10 ^ 70 +
        9053663913148230981393733580602988174287446584190825392373407180050061) * 10 ^ 70 +
        2610661271362326772731655130384220280062992470772026964471317008739576) * 10 ^ 70 +
        1024814407330634522438484307253706755010667421120107660604568913252966) * 10 ^ 70 +
        5432413319286638193347944694152564787061093173962555561536362922314966) * 10 ^ 70 +
        0061832503585355181616467356673495807047762477806479167535602409557841) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 263 = 90 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_262_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_263_prefix_zero :
    (∑ x ∈ Finset.range 91,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (263 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (263 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_263 :
    recurrence5Scalar1Left.coeff 263 =
      -((((((487 * 10 ^ 70 +
        0729071828464204082241926474753183211669142212661439695192518515118651) * 10 ^ 70 +
        1005169186198258623739066075458586301183191168066520033295565187285323) * 10 ^ 70 +
        7269237155386840544950931723612776359680150766872538556540050379679419) * 10 ^ 70 +
        2378632726041672459064896238462553922003013801195533712009572506718089) * 10 ^ 70 +
        3102015680878733441293322721551598759899676973905420694824113488393482) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 264 = 91 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_263_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_264_prefix_zero :
    (∑ x ∈ Finset.range 92,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (264 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (264 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_264 :
    recurrence5Scalar1Left.coeff 264 =
      ((((((222 * 10 ^ 70 +
        7198310267056315121817761529844135418841399594479567675334598018162377) * 10 ^ 70 +
        5316195395873105990254811109032183847896837699694944191598327832333926) * 10 ^ 70 +
        2573828882975438745861240394372569628619368440327280894380245035652302) * 10 ^ 70 +
        1757993583598083776046277847779872700031399403820071219289086441283013) * 10 ^ 70 +
        6930086474790120095338220604955853361401683853922915013261015154660265) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 265 = 92 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_264_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_265_prefix_zero :
    (∑ x ∈ Finset.range 93,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (265 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (265 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_265 :
    recurrence5Scalar1Left.coeff 265 =
      -((((((85 * 10 ^ 70 +
        5314375762144226069536060165964713550523288954255942399436560607961335) * 10 ^ 70 +
        3854643135081202824841720829112320211912587898608430662675081075646646) * 10 ^ 70 +
        6483583188665970705280448591226033267722040724017100051487461897006212) * 10 ^ 70 +
        3217666600113879348714934117458423910731955036416964246248881453500472) * 10 ^ 70 +
        7398084833962946599227699712587045671108256619321894609911801144372899) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 266 = 93 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_265_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_266_prefix_zero :
    (∑ x ∈ Finset.range 94,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (266 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (266 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_266 :
    recurrence5Scalar1Left.coeff 266 =
      ((((((21 * 10 ^ 70 +
        8724683466756015864577812331380156220794982442429175178532171979209909) * 10 ^ 70 +
        7474124381055743886353189932541966876677186154010581265169088156900268) * 10 ^ 70 +
        5784511502367336971465201660038517919083478437779129576357583404766770) * 10 ^ 70 +
        7397225834218392647805171220331310022539527768968240511337069091920086) * 10 ^ 70 +
        8941531185764439375587299835673088739633982393190083905322506737056443) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 267 = 94 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_266_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_267_prefix_zero :
    (∑ x ∈ Finset.range 95,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (267 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (267 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_267 :
    recurrence5Scalar1Left.coeff 267 =
      ((((((2 * 10 ^ 70 +
        7310914424668234902244140160964724289641387246921365976809927060998837) * 10 ^ 70 +
        3210170628904984699643775292993160978879165357385548966860729211483902) * 10 ^ 70 +
        1257558661790103879230924124161840183444354989284527274654021619604332) * 10 ^ 70 +
        5936491545068689804539068804261499942076427535502035016047629866044424) * 10 ^ 70 +
        7160685193435847897231667486088959138279743484789808799926296611625757) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 268 = 95 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_267_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_268_prefix_zero :
    (∑ x ∈ Finset.range 96,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (268 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (268 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_268 :
    recurrence5Scalar1Left.coeff 268 =
      -((((((8 * 10 ^ 70 +
        7974828636579045216145074530004722734605792265489895783188678789245703) * 10 ^ 70 +
        9951694088928782639729551941824086705325757178786965749462181332965357) * 10 ^ 70 +
        4369410878785492528180461834668693523237075357552547505680915591808641) * 10 ^ 70 +
        2155890415050240652435924279859625913847958052935635258644298795177690) * 10 ^ 70 +
        0154121822950413024452198352677707736572965271072565666439457629693414) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 269 = 96 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_268_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_269_prefix_zero :
    (∑ x ∈ Finset.range 97,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (269 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (269 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_269 :
    recurrence5Scalar1Left.coeff 269 =
      ((((((7 * 10 ^ 70 +
        5261024573964025042972770290856282768730986682786564381513385462687094) * 10 ^ 70 +
        2647180685609299521999099382224295189488819066738609920176164967727120) * 10 ^ 70 +
        4771938700034602398374833058476731144147860604953223432224922709748464) * 10 ^ 70 +
        6488721412152468904678398435807364801593670056001311521856179885583151) * 10 ^ 70 +
        5040081015519024335359687457593031125742354931836847050111144278063233) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 270 = 97 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_269_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_270_prefix_zero :
    (∑ x ∈ Finset.range 98,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (270 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (270 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_270 :
    recurrence5Scalar1Left.coeff 270 =
      -((((((4 * 10 ^ 70 +
        3858563091147192607796362771466193174020445981663837694907351383983684) * 10 ^ 70 +
        0883546078756158373216742342925904527560157160700956119706215865144859) * 10 ^ 70 +
        0723298789797687939784967654774332927607990692748622264296506854817618) * 10 ^ 70 +
        1073123337496371834943415453956173893017487415318741552534097449052963) * 10 ^ 70 +
        6837392841683221484683294855993302287375511059701631398230662657813682) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 271 = 98 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_270_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_271_prefix_zero :
    (∑ x ∈ Finset.range 99,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (271 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (271 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_271 :
    recurrence5Scalar1Left.coeff 271 =
      ((((((1 * 10 ^ 70 +
        6205751627093899744478567015483179503845411965583827263286240736980826) * 10 ^ 70 +
        1652940280019225414422452986897289294875852446486024949601670867189717) * 10 ^ 70 +
        0139945716118201959079656242582023269941595725755229229306385559535138) * 10 ^ 70 +
        4067805647152502065916182695453795548191822112347500102297248996896347) * 10 ^ 70 +
        8511200809213238581893222830356437523193323404462625727535158496212819) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 272 = 99 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_271_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_272_prefix_zero :
    (∑ x ∈ Finset.range 100,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (272 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (272 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_272 :
    recurrence5Scalar1Left.coeff 272 =
      (((((1526836643284585809557228753570277671741678152864842873751849562175391 * 10 ^ 70 +
        9220980791937692791891296994719779409676343933402692646897380588865298) * 10 ^ 70 +
        0178524733542236263446983738333758490994072871782789358259785536247670) * 10 ^ 70 +
        8580513283913930480648502605921085684263261034975097334150635666743901) * 10 ^ 70 +
        0337130831278211479678344922709511195720899375418957519989885064410815) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 273 = 100 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_272_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_273_prefix_zero :
    (∑ x ∈ Finset.range 101,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (273 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (273 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_273 :
    recurrence5Scalar1Left.coeff 273 =
      -((((((1 * 10 ^ 70 +
        0133829170202144544085403197988359120655700001102871093494252589945432) * 10 ^ 70 +
        1541642243455289574833007798480186754750344032853014112752521553402318) * 10 ^ 70 +
        0058927278987946739022507802686802092354856614261560453812077151087244) * 10 ^ 70 +
        4020117057057984301090193676052760342142387149299984440057830901755550) * 10 ^ 70 +
        4447776052517211095576515260831781552011909929676717107546446102595923) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 274 = 101 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_273_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_274_prefix_zero :
    (∑ x ∈ Finset.range 102,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (274 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (274 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_274 :
    recurrence5Scalar1Left.coeff 274 =
      ((((((1 * 10 ^ 70 +
        2515033032022918397879202503603238768590350893114002717736997688779486) * 10 ^ 70 +
        9891430460343499692248643412079037260409617013733815620525514862079605) * 10 ^ 70 +
        3615329029779202988188423149666236068511433887645223960806867651682431) * 10 ^ 70 +
        4285259016860056625844960988073250119079214382772403591814622497627687) * 10 ^ 70 +
        3557649100777277941860565756354067530184311012063093502314737464403028) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 275 = 102 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_274_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_275_prefix_zero :
    (∑ x ∈ Finset.range 103,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (275 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (275 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_275 :
    recurrence5Scalar1Left.coeff 275 =
      -((((((1 * 10 ^ 70 +
        1497379270541129057963685785125597852375144312894918625518069181375440) * 10 ^ 70 +
        2102575696433124796559871162921113117099663129585820068410371272480175) * 10 ^ 70 +
        6814039304743861169111729615530344687946048306643443489612097929559681) * 10 ^ 70 +
        2635225246815574809712538772130285550137133502405873827475906304497919) * 10 ^ 70 +
        9694750575971424870417583898938316472385136900730417077761597544744701) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 276 = 103 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_275_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_276_prefix_zero :
    (∑ x ∈ Finset.range 104,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (276 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (276 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_276 :
    recurrence5Scalar1Left.coeff 276 =
      (((((9110867619404027788079986706247611619243080901768894549914865755120664 * 10 ^ 70 +
        5193982771090358457757643244594061407974163549947131692642277687107850) * 10 ^ 70 +
        2890354073035759865753314086275238300882536483955505827806187949322490) * 10 ^ 70 +
        0430400933159987580546125271436743989104917217091719913340074905144644) * 10 ^ 70 +
        5313321771845086535754881514940902522646428861606121006771059994874275) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 277 = 104 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_276_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_277_prefix_zero :
    (∑ x ∈ Finset.range 105,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (277 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (277 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_277 :
    recurrence5Scalar1Left.coeff 277 =
      -(((((6547031682670759945959551198889679541806770957855636089999950322872950 * 10 ^ 70 +
        1521875448410640721226569485008065221348732146186877525655739893607614) * 10 ^ 70 +
        9045948831047155870003855469740571350098383415162422794100315506837519) * 10 ^ 70 +
        3187061212470660171463963771849065485007415788098028931278700972328808) * 10 ^ 70 +
        4357036557855202250700221614485843155053174795773963207669095339215602) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 278 = 105 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_277_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_278_prefix_zero :
    (∑ x ∈ Finset.range 106,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (278 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (278 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_278 :
    recurrence5Scalar1Left.coeff 278 =
      (((((4365222078605022058749043402618498314486232108031235595003678761903658 * 10 ^ 70 +
        7189265369639117834041242120846368402775301946543130112461353099560362) * 10 ^ 70 +
        7672320361582236904452832192088967084756935311532674856406643241916720) * 10 ^ 70 +
        1025144279021467644228712937536412054977073325994396545356637949932925) * 10 ^ 70 +
        9364737154354479215077886843987651885606089080886283833121671712690100) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 279 = 106 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_278_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_279_prefix_zero :
    (∑ x ∈ Finset.range 107,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (279 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (279 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_279 :
    recurrence5Scalar1Left.coeff 279 =
      -(((((2733086857543662702172581324565991126566694867422391187662499047611097 * 10 ^ 70 +
        9731579889797245113482476891801280357918033502822644000573824695665175) * 10 ^ 70 +
        3860181562731561069518335115156230426535563042423317499112292898780230) * 10 ^ 70 +
        3314924366024766347065738222283785842927648220792569202713351907699232) * 10 ^ 70 +
        5660419198673521439965165488035918036975467728104997654697588342382611) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 280 = 107 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_279_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_280_prefix_zero :
    (∑ x ∈ Finset.range 108,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (280 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (280 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_280 :
    recurrence5Scalar1Left.coeff 280 =
      (((((1617311724589223564164708011548569776900491036652427201788084557047915 * 10 ^ 70 +
        8853974988012272650906088661100788780960587466150185460231711650090659) * 10 ^ 70 +
        5218751015906463590871161036223432389844809773577981812638071817609796) * 10 ^ 70 +
        5256615067299217071019461119928256544038922724997411657869978393309035) * 10 ^ 70 +
        3339569208190642610696689125787416273777623439939458087897982479154307) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 281 = 108 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_280_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_281_prefix_zero :
    (∑ x ∈ Finset.range 109,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (281 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (281 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_281 :
    recurrence5Scalar1Left.coeff 281 =
      -(((((907337958581159941308080178833617747338163004744264285285762781578770 * 10 ^ 70 +
        6702269279656752440300484315762730373337078622735261143118515714776627) * 10 ^ 70 +
        9956693332935145378099679326441346720442989604721239280469085773517878) * 10 ^ 70 +
        8232280716358002111403154974801439265203157404750509608028007351391146) * 10 ^ 70 +
        5671446239119772664088845519542728640260261068455882904015403278891928) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 282 = 109 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_281_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_282_prefix_zero :
    (∑ x ∈ Finset.range 110,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (282 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (282 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_282 :
    recurrence5Scalar1Left.coeff 282 =
      (((((482865206001429775073072155698744527656018220857925931151678856260969 * 10 ^ 70 +
        6474809662302618020469525815896398215911135801737652391194132059002765) * 10 ^ 70 +
        1923357378713827857082674208732649104421337049454007203015052025540330) * 10 ^ 70 +
        4863277414333907456824696142904908983833715005095302963755938150309359) * 10 ^ 70 +
        0446450366081867068772276302191466098563101893621554935927885423367107) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 283 = 110 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_282_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_283_prefix_zero :
    (∑ x ∈ Finset.range 111,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (283 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (283 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_283 :
    recurrence5Scalar1Left.coeff 283 =
      -(((((243320445935733634278819694008591105914739919925494084936149241970103 * 10 ^ 70 +
        1823668788890331816501255212899829362879935212849287931590259594648667) * 10 ^ 70 +
        6583161783852439250275887160263199193096610215778830364106313698574745) * 10 ^ 70 +
        5716022295119178370406080947849688372950245175275020207379342148179283) * 10 ^ 70 +
        8282422320399271360955086752833976549786121349200088895132560359825994) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 284 = 111 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_283_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_284_prefix_zero :
    (∑ x ∈ Finset.range 112,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (284 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (284 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_284 :
    recurrence5Scalar1Left.coeff 284 =
      (((((115558595931475572102600784963162801827721435810758743442884687306929 * 10 ^ 70 +
        8682898737257485066808854315870982787811459766699870364298621817326714) * 10 ^ 70 +
        8560612700102350555259601299619699226001961181245726518585258451127540) * 10 ^ 70 +
        2643512329820858738811155343990919468376376202296664729367554306529454) * 10 ^ 70 +
        6466233837686909969928566836283031434558780949654123110490750689048047) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 285 = 112 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_284_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_285_prefix_zero :
    (∑ x ∈ Finset.range 113,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (285 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (285 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_285 :
    recurrence5Scalar1Left.coeff 285 =
      -(((((51264651380298349354946226170643545994541914944973392448145878745744 * 10 ^ 70 +
        9934649419379023035654573090182202441326035084153716912187085248439834) * 10 ^ 70 +
        0788735204755738109034501439197664865961224363560386724471056686119247) * 10 ^ 70 +
        8777207225870768770266351741959903485385417697020549697051474664013448) * 10 ^ 70 +
        8176910928676076822219205158138804888186095358358148898594639025918464) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 286 = 113 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_285_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_286_prefix_zero :
    (∑ x ∈ Finset.range 114,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (286 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (286 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_286 :
    recurrence5Scalar1Left.coeff 286 =
      (((((20891846331923529373470816168550423081850019602129711633832929247819 * 10 ^ 70 +
        9789807807103644776715828961162787027490049942671397100339889082573478) * 10 ^ 70 +
        9766528518853563664418668745866641759259384435574797614716292499072753) * 10 ^ 70 +
        6477849517830250671067315324846812110280266984095878806753378622928415) * 10 ^ 70 +
        8803149233058830874004034376026566097022726855456930414824948577392102) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 287 = 114 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_286_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_287_prefix_zero :
    (∑ x ∈ Finset.range 115,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (287 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (287 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_287 :
    recurrence5Scalar1Left.coeff 287 =
      -(((((7559754407203643252974069893684284451675926889950375668332078012935 * 10 ^ 70 +
        8916561987332727025543801270281265197642770345571004516311072359165789) * 10 ^ 70 +
        4842997158458325336413872647869693649842184034633847662030199400375249) * 10 ^ 70 +
        5723952492600374392119249553194313116613817984085566536060840565904898) * 10 ^ 70 +
        9087845695833612300271630215383392967694619986230532788313350542081962) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 288 = 115 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_287_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_288_prefix_zero :
    (∑ x ∈ Finset.range 116,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (288 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (288 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_288 :
    recurrence5Scalar1Left.coeff 288 =
      (((((2229537039400515196598088284492965117400730099367973081510597504769 * 10 ^ 70 +
        4758440047321629680534940177955310674512199604026521601579320509944963) * 10 ^ 70 +
        0327527583319801205918295276029815972403660957004780205088397920073409) * 10 ^ 70 +
        8032679059871232892485739528084134272240594504513553240321042220058874) * 10 ^ 70 +
        2450072333850878823956051212294653613849415252532586042672703416297811) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 289 = 116 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_288_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_289_prefix_zero :
    (∑ x ∈ Finset.range 117,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (289 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (289 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_289 :
    recurrence5Scalar1Left.coeff 289 =
      -(((((370397083782312056007615663410702336911083748305331665494160235649 * 10 ^ 70 +
        7523752358645949895658404325244784726337298663709911555958892687546853) * 10 ^ 70 +
        6916044702546801827361605770388431067964796950278881730519918027824156) * 10 ^ 70 +
        9925353623650425848963459978948474884814936725424930902570273468401586) * 10 ^ 70 +
        5459287574599474532414577026374903942445561974679287888376773537796588) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 290 = 117 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_289_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_290_prefix_zero :
    (∑ x ∈ Finset.range 118,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (290 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (290 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_290 :
    recurrence5Scalar1Left.coeff 290 =
      -(((((130767554798518065652868967854149801387033187536971089978401801917 * 10 ^ 70 +
        6624360009299923291672677315352672232438206513514293794123299977761830) * 10 ^ 70 +
        8039689769099009980774999393812125374872221684802597616884425395145659) * 10 ^ 70 +
        1296613733711180319169304430441687508112764620176889808411744597327406) * 10 ^ 70 +
        5644272261759406230739165807649175212982463348238284969799884261636404) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 291 = 118 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_290_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_291_prefix_zero :
    (∑ x ∈ Finset.range 119,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (291 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (291 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_291_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (291 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_291 :
    recurrence5Scalar1Left.coeff 291 =
      (((((178514059618816975889886451484879285283355666311554170230934592327 * 10 ^ 70 +
        4739871895801244628297041866927746281104524694879791134722653399238643) * 10 ^ 70 +
        9687984801722681571059340805157545063167581499448511391759859208986449) * 10 ^ 70 +
        7126363749891043094634127973045977737965415050177728750635564188616885) * 10 ^ 70 +
        3348112975850307051570279715984411786169130671070690607416625498526550) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 292 = 119 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 12 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_291_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_291_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_292_prefix_zero :
    (∑ x ∈ Finset.range 120,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (292 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (292 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_292_suffix_zero :
    (∑ x ∈ Finset.range 2,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (292 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_292 :
    recurrence5Scalar1Left.coeff 292 =
      -(((((118090670843970618087480884968220778441207392036893743223487860849 * 10 ^ 70 +
        5191732201084554582321836555882259067862627088292549618514992616310488) * 10 ^ 70 +
        7815055998290180214378432340223976674771990694538230994717372701163075) * 10 ^ 70 +
        2414536808026415379901298026806442024408531963184215116442165998176651) * 10 ^ 70 +
        7071587672967307834468861550481480289914801413783583235450136593899598) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 293 = 120 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 11 +
      2 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_292_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_292_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_293_prefix_zero :
    (∑ x ∈ Finset.range 121,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (293 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (293 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_293_suffix_zero :
    (∑ x ∈ Finset.range 3,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (293 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_293 :
    recurrence5Scalar1Left.coeff 293 =
      (((((58859314839185450393615045532974254959585681660835644191699859558 * 10 ^ 70 +
        8176417686149507204967599819877869391392165097213821485591240120822258) * 10 ^ 70 +
        4435611133669762649412622594400070857352023166455571385052230844505723) * 10 ^ 70 +
        3872999948958434172872333151379887710610128966854505438346483173041575) * 10 ^ 70 +
        7412711498445268170551030352498240775520138502902211094066397576100209) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 294 = 121 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 10 +
      3 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_293_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_293_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_294_prefix_zero :
    (∑ x ∈ Finset.range 122,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (294 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (294 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_294_suffix_zero :
    (∑ x ∈ Finset.range 4,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (294 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_294 :
    recurrence5Scalar1Left.coeff 294 =
      -(((((22665288734480619498590937113970508631347788451270734416039025819 * 10 ^ 70 +
        8016058538239491960207701697997608179036491167313887791896081120054624) * 10 ^ 70 +
        6049653152608746641214591121123775914778385668074815812108619855689668) * 10 ^ 70 +
        1785322373980403968603297346930323883982661354782131410274400602375669) * 10 ^ 70 +
        2023492158886552560555083198573930968444359298962577385249997016135150) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 295 = 122 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 9 +
      4 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_294_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_294_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_295_prefix_zero :
    (∑ x ∈ Finset.range 123,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (295 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (295 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_295_suffix_zero :
    (∑ x ∈ Finset.range 5,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (295 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_295 :
    recurrence5Scalar1Left.coeff 295 =
      (((((5371343560771122312312263705656695995190915313709679059787868166 * 10 ^ 70 +
        2844044503267667737746973461248538058527635101822998263016388004979915) * 10 ^ 70 +
        5413197500879351911260700299679234180467323129402772362004455483219114) * 10 ^ 70 +
        2126134094109349955144419806543727338775456444686133545285369706097233) * 10 ^ 70 +
        5599105538472533257936449360298702776309580094716433569036321785153047) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 296 = 123 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 8 +
      5 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_295_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_295_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_296_prefix_zero :
    (∑ x ∈ Finset.range 124,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (296 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (296 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_296_suffix_zero :
    (∑ x ∈ Finset.range 6,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (296 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_296 :
    recurrence5Scalar1Left.coeff 296 =
      (((((1048040281530802882726643334773114312898726390195436168732044861 * 10 ^ 70 +
        5802823550033834907942004074341304798094076668121250184225653166707622) * 10 ^ 70 +
        4000749099188536269115752007962769652942486899079315304680093165686155) * 10 ^ 70 +
        5033210126650262996001076926844720622276184290426633084511418784231001) * 10 ^ 70 +
        4294705142834202142377195495476974933080831899593542302693128748252638) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 297 = 124 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 7 +
      6 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_296_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_296_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_297_prefix_zero :
    (∑ x ∈ Finset.range 125,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (297 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (297 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_297_suffix_zero :
    (∑ x ∈ Finset.range 7,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (297 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_297 :
    recurrence5Scalar1Left.coeff 297 =
      -(((((2462540252176658310094670950087407447183186587462186253906940168 * 10 ^ 70 +
        2097879902191906150397283395844115035381968421807860695517613046795212) * 10 ^ 70 +
        2478870417938624428762299523203617324085904863447331228367799102850975) * 10 ^ 70 +
        7736142196712900722129586902813941291290569118518460156913015422929706) * 10 ^ 70 +
        1151605744826166915942125863827671246277050377513802934986258005830253) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 298 = 125 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 6 +
      7 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_297_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_297_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_298_prefix_zero :
    (∑ x ∈ Finset.range 126,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (298 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (298 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_298_suffix_zero :
    (∑ x ∈ Finset.range 8,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (298 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_298 :
    recurrence5Scalar1Left.coeff 298 =
      (((((2088779029269609461711951019545572344126906942859841436155806137 * 10 ^ 70 +
        1379312852786196522909353332966231435958185704860484458138707048624495) * 10 ^ 70 +
        1593422196368183821976972021482565241431183750173835721434740094982840) * 10 ^ 70 +
        1117587860213620879215729240897968743564642694799016564952784096729663) * 10 ^ 70 +
        0286433746029776402099314541471069414203229102214799035873979012705838) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 299 = 126 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 5 +
      8 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_298_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_298_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_299_prefix_zero :
    (∑ x ∈ Finset.range 127,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (299 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (299 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_299_suffix_zero :
    (∑ x ∈ Finset.range 9,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (299 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_299 :
    recurrence5Scalar1Left.coeff 299 =
      -(((((1356506012992018127508370072403130830832716714475496657630524063 * 10 ^ 70 +
        5187513412688201258613785678571792214543239260996689761881382785595645) * 10 ^ 70 +
        7749773852773239898545290958256588025365038628915950700305741954548000) * 10 ^ 70 +
        3514667574669825718216324387930229070839528873591069768186746533964358) * 10 ^ 70 +
        3141480951526516014633277081171238643055293717224215072378700647860903) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 300 = 127 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 4 +
      9 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_299_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_299_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_300_prefix_zero :
    (∑ x ∈ Finset.range 128,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (300 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (300 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_300_suffix_zero :
    (∑ x ∈ Finset.range 10,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (300 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_300 :
    recurrence5Scalar1Left.coeff 300 =
      (((((756105846436141052096318465374375037968831609296794113118169938 * 10 ^ 70 +
        4052718521356756633407466995020766503104501763330321908711971289150012) * 10 ^ 70 +
        0120095768069089743379355222552226899381918952697206297530336714758464) * 10 ^ 70 +
        6791603050262656708317725390252069476664725886462434302510514900949156) * 10 ^ 70 +
        8866448298562858043918799751554914762741546679081747136528559328257653) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 301 = 128 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 3 +
      10 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_300_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_300_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_301_prefix_zero :
    (∑ x ∈ Finset.range 129,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (301 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (301 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_301_suffix_zero :
    (∑ x ∈ Finset.range 11,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (301 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_301 :
    recurrence5Scalar1Left.coeff 301 =
      -(((((374229447558964487601648763172862485416294923565224038313948825 * 10 ^ 70 +
        8576229160778652866383861897683480105047388946776839524625517185558865) * 10 ^ 70 +
        3770674249945834419585971110735191628302693847732746188161031941365700) * 10 ^ 70 +
        9706883934930009328463827753072962429077419163081981503617992254621114) * 10 ^ 70 +
        8400493171933309898488568414739988006349233069659487651358524763663451) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 302 = 129 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 2 +
      11 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_301_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_301_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_302_prefix_zero :
    (∑ x ∈ Finset.range 130,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (302 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (302 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_302_suffix_zero :
    (∑ x ∈ Finset.range 12,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (302 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_302 :
    recurrence5Scalar1Left.coeff 302 =
      (((((165154596240348571418097508611731584288224095912272309263893706 * 10 ^ 70 +
        3787691113181497881449958878612925473516586736267145707809484428230823) * 10 ^ 70 +
        8899688580799652429492107980855449212954900784419004393866020864222886) * 10 ^ 70 +
        1678285028871771495160265201645059035082845445805461129803778205361149) * 10 ^ 70 +
        2131240936567144877442777040759613425781136120180745399502023605296272) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 303 = 130 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 1 +
      12 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_302_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_302_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_303_prefix_zero :
    (∑ x ∈ Finset.range 131,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (303 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (303 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_303_suffix_zero :
    (∑ x ∈ Finset.range 13,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (303 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_303 :
    recurrence5Scalar1Left.coeff 303 =
      -(((((63571530939634342551623887525909370161080842376411337133510479 * 10 ^ 70 +
        4127179734169885749611388611082798303019888032513424832054831050724081) * 10 ^ 70 +
        6141511422752438581531799698656408289361528640377066802219970800660813) * 10 ^ 70 +
        9255335592527367065590567546618700481264336643327275736571964680372650) * 10 ^ 70 +
        4468914557389508130257452871279836478508041299207795330445083900490883) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 304 = 131 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_303_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_303_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_304_prefix_zero :
    (∑ x ∈ Finset.range 132,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (304 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (304 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_304_suffix_zero :
    (∑ x ∈ Finset.range 14,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (304 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_304 :
    recurrence5Scalar1Left.coeff 304 =
      (((((19726077273257070347658113864001185933343065742877262110752692 * 10 ^ 70 +
        4315717688120930064991995306255445173474352264061734779943736818033899) * 10 ^ 70 +
        2699627036875803332920931492398735527215998147524134349584369309652125) * 10 ^ 70 +
        3706288988875639488279766231522376546828575026058576639172386221462691) * 10 ^ 70 +
        6839477398340377563034588640872858204035369060427289996153546837742242) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 305 = 132 +
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
    rw [show 45 = 31 +
      14 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_304_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_304_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_305_prefix_zero :
    (∑ x ∈ Finset.range 133,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (305 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (305 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_305_suffix_zero :
    (∑ x ∈ Finset.range 15,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (305 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_305 :
    recurrence5Scalar1Left.coeff 305 =
      -(((((3381585579480406033487393224733970341185179962310727944958076 * 10 ^ 70 +
        3552637649835147187303705253431891662004760021902435263932812161766342) * 10 ^ 70 +
        9608317936875057966292399056605236227951260367902786943779359275586067) * 10 ^ 70 +
        9769518035177489639994012551278992489839315878240082825741810153556753) * 10 ^ 70 +
        1713341353977503047600114072039887797980344967190538192648133161149745) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 306 = 133 +
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
    rw [show 45 = 30 +
      15 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_305_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_305_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_306_prefix_zero :
    (∑ x ∈ Finset.range 134,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (306 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (306 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_306_suffix_zero :
    (∑ x ∈ Finset.range 16,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (306 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_306 :
    recurrence5Scalar1Left.coeff 306 =
      -(((((1378207091754196579590459637035754282713798098399469912320557 * 10 ^ 70 +
        0248005650189340187569706441523647457313430890626748397236561422748020) * 10 ^ 70 +
        7199763468603672429414371139261174806067971749393632674970189206293427) * 10 ^ 70 +
        1924595967222232157929350839778788347746032656065513947851525158128358) * 10 ^ 70 +
        6383330185491807641095418515078057660092457330195149567128133894505852) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 307 = 134 +
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
    rw [show 45 = 29 +
      16 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_306_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_306_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_307_prefix_zero :
    (∑ x ∈ Finset.range 135,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (307 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (307 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_307_suffix_zero :
    (∑ x ∈ Finset.range 17,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (307 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_307 :
    recurrence5Scalar1Left.coeff 307 =
      (((((1974454214555040627532777705097489669620088288613134128329937 * 10 ^ 70 +
        5666113777545568472416255910940415028323013111862960786702119354455383) * 10 ^ 70 +
        4137791923623993478269352275377491935881349492944617108212307715700092) * 10 ^ 70 +
        2447806826640068165787347224261601643234070607082853406894249462796602) * 10 ^ 70 +
        2524468541373975275777728877190975376010604686853815338417056609031777) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 308 = 135 +
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
    rw [show 45 = 28 +
      17 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_307_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_307_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_308_prefix_zero :
    (∑ x ∈ Finset.range 136,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (308 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (308 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_308_suffix_zero :
    (∑ x ∈ Finset.range 18,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (308 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_308 :
    recurrence5Scalar1Left.coeff 308 =
      -(((((1450729725418397169804220675238564145255613499416066090185855 * 10 ^ 70 +
        3472512019702186786584789986695108040400963720605154322023582206749490) * 10 ^ 70 +
        6200043592489712811975651599102033996723054264799407070612166988956130) * 10 ^ 70 +
        7537471955195951479780794828519841225832324207199015824679697430182507) * 10 ^ 70 +
        5482154609999840367294215492394470127062683568873070476639301529069733) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 309 = 136 +
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
    rw [show 45 = 27 +
      18 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_308_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_308_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_309_prefix_zero :
    (∑ x ∈ Finset.range 137,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (309 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (309 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_309_suffix_zero :
    (∑ x ∈ Finset.range 19,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (309 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_309 :
    recurrence5Scalar1Left.coeff 309 =
      (((((855703301204149643729306669880631034970003684531521573146381 * 10 ^ 70 +
        4932795568157412660954503204959628815793408325088585485940835427037168) * 10 ^ 70 +
        5477305203586153481897118141700881820518721498873295036640322598746835) * 10 ^ 70 +
        2013002295810843846247706217406782234935628625722271376740718987162770) * 10 ^ 70 +
        2467780922808392441213160303620110441717020207004510903620661433906841) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 310 = 137 +
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
    rw [show 45 = 26 +
      19 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_309_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_309_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_310_prefix_zero :
    (∑ x ∈ Finset.range 138,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (310 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (310 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_310_suffix_zero :
    (∑ x ∈ Finset.range 20,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (310 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_310 :
    recurrence5Scalar1Left.coeff 310 =
      -(((((443790074535435720084494197361584890965118755610827655029022 * 10 ^ 70 +
        2438543927763735058887405436917087385085384718249875628886472095153363) * 10 ^ 70 +
        9724510570873830141537308154620327639512031476478811508111162640188714) * 10 ^ 70 +
        8913429934740656207198056029136182761361931038808578026534745613879135) * 10 ^ 70 +
        7437522901996624912167812656486102557541071671483393564627012425951018) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 311 = 138 +
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
    rw [show 45 = 25 +
      20 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_310_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_310_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_311_prefix_zero :
    (∑ x ∈ Finset.range 139,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (311 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (311 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_311_suffix_zero :
    (∑ x ∈ Finset.range 21,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (311 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_311 :
    recurrence5Scalar1Left.coeff 311 =
      (((((208973385784183754209655078506653062547934970594841308766777 * 10 ^ 70 +
        8820131847678744224580871027239746599983325236230210222691778224913928) * 10 ^ 70 +
        8250853302945970497703356259204183135483381346012087552918488946791666) * 10 ^ 70 +
        9481741792508248000428035136685456092418239901462128459327941230345245) * 10 ^ 70 +
        1813811097665923491370162318740616986458385588271369661723301972339805) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 312 = 139 +
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
    rw [show 45 = 24 +
      21 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_311_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_311_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_312_prefix_zero :
    (∑ x ∈ Finset.range 140,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (312 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (312 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_312_suffix_zero :
    (∑ x ∈ Finset.range 22,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (312 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_312 :
    recurrence5Scalar1Left.coeff 312 =
      -(((((90415767478513818269526424687891084452957592835608767858215 * 10 ^ 70 +
        0988903067611121579795889827324075891308284512071241127573453683103097) * 10 ^ 70 +
        8922692660323482053397137180229262635943803371825478514824640629174158) * 10 ^ 70 +
        6646029252549318610919589033301359245567885696390706559063007469036126) * 10 ^ 70 +
        2057791909447573089655471327982906316097737079927852302696663458914545) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 313 = 140 +
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
    rw [show 45 = 23 +
      22 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_312_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_312_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_313_prefix_zero :
    (∑ x ∈ Finset.range 141,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (313 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (313 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_313_suffix_zero :
    (∑ x ∈ Finset.range 23,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (313 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_313 :
    recurrence5Scalar1Left.coeff 313 =
      (((((35984903955221497912636495488244696715561693768501512446797 * 10 ^ 70 +
        1442234191910124215598207783228788469923716610011558265274390595360689) * 10 ^ 70 +
        6425970084731621110757402225543497167169065962121446802518095197654394) * 10 ^ 70 +
        9558509467636814640054170762788367676520941856147552897047196969499002) * 10 ^ 70 +
        9800122272394233558806045740020356195370105387659261796534855935194640) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 314 = 141 +
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
    rw [show 45 = 22 +
      23 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_313_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_313_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_314_prefix_zero :
    (∑ x ∈ Finset.range 142,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (314 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (314 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_314_suffix_zero :
    (∑ x ∈ Finset.range 24,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (314 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_314 :
    recurrence5Scalar1Left.coeff 314 =
      -(((((13065012022536162726406840019914786665285444249719207758126 * 10 ^ 70 +
        2261232586564237399493601161921787870001517009834985590794790914531691) * 10 ^ 70 +
        3949701622852855881115945763438643643931698554184017941869426964451722) * 10 ^ 70 +
        2736099025120354565925422372324680078033091801338537864815907997793582) * 10 ^ 70 +
        3497467140739233062719192072654377428303982506740073699108448777623787) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 315 = 142 +
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
    rw [show 45 = 21 +
      24 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_314_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_314_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_315_prefix_zero :
    (∑ x ∈ Finset.range 143,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (315 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (315 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_315_suffix_zero :
    (∑ x ∈ Finset.range 25,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (315 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_315 :
    recurrence5Scalar1Left.coeff 315 =
      (((((4234347959630293650296446610374373433681618191223015916301 * 10 ^ 70 +
        4606033783604242529160993489934300373465887012101465419888921069723178) * 10 ^ 70 +
        4197986735251927383444878159708931003621125195790399999289843211584865) * 10 ^ 70 +
        8146269245330863090301023849724955742153688814910679781315199912943820) * 10 ^ 70 +
        5722356027250113681438676197996370867280089624750477894916587271274092) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 316 = 143 +
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
    rw [show 45 = 20 +
      25 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_315_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_315_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_316_prefix_zero :
    (∑ x ∈ Finset.range 144,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (316 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (316 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_316_suffix_zero :
    (∑ x ∈ Finset.range 26,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (316 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_316 :
    recurrence5Scalar1Left.coeff 316 =
      -(((((1165161055961261708565838717406081149734318315185066608087 * 10 ^ 70 +
        7352469939590328183777132962104125921582525110449031923670352045628590) * 10 ^ 70 +
        9620097763614075715031663908594846088815362264039742496599921511559453) * 10 ^ 70 +
        0237956414834122922795276349087943670161222397728453155133147280884404) * 10 ^ 70 +
        5821132711147603519044965774151057621055939539228911167695871849664293) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 317 = 144 +
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
    rw [show 45 = 19 +
      26 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_316_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_316_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_317_prefix_zero :
    (∑ x ∈ Finset.range 145,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (317 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (317 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_317_suffix_zero :
    (∑ x ∈ Finset.range 27,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (317 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_317 :
    recurrence5Scalar1Left.coeff 317 =
      (((((236228280230848152387132890983409632425312629009280831842 * 10 ^ 70 +
        5483473330304049909812975338376500335617752766637565691654438935584284) * 10 ^ 70 +
        1820117119000185272751444754183694452678891389086063433117658541101478) * 10 ^ 70 +
        8747446431771425723291252826445155530279718250002949185949111547686656) * 10 ^ 70 +
        7419506163859017000067132493921832347884575254504702693607902654895906) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 318 = 145 +
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
    rw [show 45 = 18 +
      27 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_317_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_317_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_318_prefix_zero :
    (∑ x ∈ Finset.range 146,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (318 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (318 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_318_suffix_zero :
    (∑ x ∈ Finset.range 28,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (318 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_318 :
    recurrence5Scalar1Left.coeff 318 =
      -(((((13314716498157949721292114574078620239805541018190597779 * 10 ^ 70 +
        7436374943216673476130584920132701219980375137900590031299930007553766) * 10 ^ 70 +
        1326589164527734606847982487858860612280550716583318190266061813879605) * 10 ^ 70 +
        5979840838770407427488370654650605744919287132923427982218818127159359) * 10 ^ 70 +
        8176610690735698784048887867583570791040204561380305718988176153807155) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 319 = 146 +
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
    rw [show 45 = 17 +
      28 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_318_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_318_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_319_prefix_zero :
    (∑ x ∈ Finset.range 147,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (319 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (319 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_319_suffix_zero :
    (∑ x ∈ Finset.range 29,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (319 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_319 :
    recurrence5Scalar1Left.coeff 319 =
      -(((((14554534841556585898491018177400443681176494789233817960 * 10 ^ 70 +
        6851709996634407448240474054153052556543005707595077635278852501737117) * 10 ^ 70 +
        3479560767490580501651377547156781698431352980944641230094082964038496) * 10 ^ 70 +
        7659806391506173513493150494034322156558948353876144153652371935411317) * 10 ^ 70 +
        9738452333125507934142242413764991944398786222977249490543847735411641) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 320 = 147 +
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
    rw [show 45 = 16 +
      29 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_319_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_319_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_320_prefix_zero :
    (∑ x ∈ Finset.range 148,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (320 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (320 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_320_suffix_zero :
    (∑ x ∈ Finset.range 30,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (320 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_320 :
    recurrence5Scalar1Left.coeff 320 =
      (((((5383361366846296414431795926069713142729503601041413389 * 10 ^ 70 +
        5988080559637849635805750608724929240260434745734652685954032027127558) * 10 ^ 70 +
        6156761838044088967502889130750535474904145961135762598127143030779559) * 10 ^ 70 +
        6115749824911506906268856720487135926391115411170944190905626092536366) * 10 ^ 70 +
        4427956068113611609451141240976462251958641880060328165316529015289920) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 321 = 148 +
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
    rw [show 45 = 15 +
      30 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_320_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_320_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_321_prefix_zero :
    (∑ x ∈ Finset.range 149,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (321 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (321 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_321_suffix_zero :
    (∑ x ∈ Finset.range 31,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (321 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_321 :
    recurrence5Scalar1Left.coeff 321 =
      (((((2565257491298982346136656388595391760323138053373846649 * 10 ^ 70 +
        7073484022124578702876642674518348479593739208524861751799877535488094) * 10 ^ 70 +
        4701025059775966106926114903689561476911964604001812595560544790321607) * 10 ^ 70 +
        7250773160903364531250379475716473050941409190651419590245151313503592) * 10 ^ 70 +
        7583947633812200410806028172911579558894460348162357697741978306530059) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 322 = 149 +
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
    rw [show 45 = 14 +
      31 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_321_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_321_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_322_prefix_zero :
    (∑ x ∈ Finset.range 150,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (322 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (322 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_322_suffix_zero :
    (∑ x ∈ Finset.range 32,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (322 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_322 :
    recurrence5Scalar1Left.coeff 322 =
      -(((((5075100537862379209502160947482610629272943182990117257 * 10 ^ 70 +
        7562629444935154480375550839378271196710259062720800897483803621105076) * 10 ^ 70 +
        7650511773428090791399546189032811953861231147499944706434246822564581) * 10 ^ 70 +
        1703663307324846546640154131327572199982959901231084621842173553033789) * 10 ^ 70 +
        6046636342689486381729256705380941730788614787553471629319469356926588) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 323 = 150 +
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
    rw [show 45 = 13 +
      32 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_322_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_322_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_323_prefix_zero :
    (∑ x ∈ Finset.range 151,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (323 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (323 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_323_suffix_zero :
    (∑ x ∈ Finset.range 33,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (323 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_323 :
    recurrence5Scalar1Left.coeff 323 =
      (((((4575596334944438932507132947879805085283008454056506730 * 10 ^ 70 +
        9539067289379851237480003890530652762094856143673619106358792545392744) * 10 ^ 70 +
        0989189545471408344452690297432736319405041923693780089110650567925786) * 10 ^ 70 +
        3972723557757430095464545203283599329331271075284437681133898364969225) * 10 ^ 70 +
        1583423235488198771924913507158432718881511138183295409258368194813225) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 324 = 151 +
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
    rw [show 45 = 12 +
      33 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_323_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_323_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_324_prefix_zero :
    (∑ x ∈ Finset.range 152,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (324 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (324 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_324_suffix_zero :
    (∑ x ∈ Finset.range 34,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (324 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_324 :
    recurrence5Scalar1Left.coeff 324 =
      -(((((3205808800077067169396435231937583851986579361292641064 * 10 ^ 70 +
        7782198449465477456999297484392022584709112811257587559665555449265166) * 10 ^ 70 +
        0688257864293164072750160933544219391428332136542106916742559421598940) * 10 ^ 70 +
        7394131012260721367618701647454314573594607145195997522258541519838226) * 10 ^ 70 +
        9461963678180048897455176082712666913512102735753621020785412548498823) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 325 = 152 +
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
    rw [show 45 = 11 +
      34 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_324_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_324_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_325_prefix_zero :
    (∑ x ∈ Finset.range 153,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (325 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (325 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_325_suffix_zero :
    (∑ x ∈ Finset.range 35,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (325 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_325 :
    recurrence5Scalar1Left.coeff 325 =
      (((((1953972900084399973797998182103844734849785500854804920 * 10 ^ 70 +
        8872492909447023301126937591493203274248017009341105337763059852337002) * 10 ^ 70 +
        6437925779746759694726955976557133181518687692786947238471712607816704) * 10 ^ 70 +
        8930078089518556566410229684791717861002307936769418332602585976203031) * 10 ^ 70 +
        8975785030089856303301866450329530928358038822627595932320847898787267) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 326 = 153 +
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
    rw [show 45 = 10 +
      35 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_325_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_325_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_326_prefix_zero :
    (∑ x ∈ Finset.range 154,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (326 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (326 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_326_suffix_zero :
    (∑ x ∈ Finset.range 36,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (326 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_326 :
    recurrence5Scalar1Left.coeff 326 =
      -(((((1083926748606048133783584879366020621454949621616129355 * 10 ^ 70 +
        3432957452044197626381268215343906609158715623604795334140684569841251) * 10 ^ 70 +
        0972544531292556374127057141919630972169193342140121148770620031863473) * 10 ^ 70 +
        9341986242492892910904934502031132130746378867175736202837007602937431) * 10 ^ 70 +
        5211806439570861489147455233564738001737495304778805472762495670476141) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 327 = 154 +
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
    rw [show 45 = 9 +
      36 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_326_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_326_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_327_prefix_zero :
    (∑ x ∈ Finset.range 155,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (327 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (327 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_327_suffix_zero :
    (∑ x ∈ Finset.range 37,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (327 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_327 :
    recurrence5Scalar1Left.coeff 327 =
      (((((559922127412954271406548777427564198509569936389663116 * 10 ^ 70 +
        4680423172824734884836716417906825624554120435195389852351715503156338) * 10 ^ 70 +
        0169185470634047024062616584424028467412201521259584503533394288622049) * 10 ^ 70 +
        1169366574797821828002497215967356332081556380896273699587403770129651) * 10 ^ 70 +
        2934705683180675046669305281700992927890317846470137671655307211195682) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 328 = 155 +
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
    rw [show 45 = 8 +
      37 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_327_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_327_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_328_prefix_zero :
    (∑ x ∈ Finset.range 156,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (328 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (328 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_328_suffix_zero :
    (∑ x ∈ Finset.range 38,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (328 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_328 :
    recurrence5Scalar1Left.coeff 328 =
      -(((((272898739331745300992940940271687717344716531534780692 * 10 ^ 70 +
        5095977656064333054821979352219937799020120081167861697381151105162287) * 10 ^ 70 +
        6060928351647134602412374506228701209756529682800612362158583745985704) * 10 ^ 70 +
        3001163639713365180028207738742003812617853430459499878780807936782085) * 10 ^ 70 +
        0318924586325856367128332547154347375465022006889843863390431589351057) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 329 = 156 +
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
    rw [show 45 = 7 +
      38 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_328_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_328_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_329_prefix_zero :
    (∑ x ∈ Finset.range 157,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (329 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (329 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Left_coeff_329_suffix_zero :
    (∑ x ∈ Finset.range 39,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient1.coeff (329 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_329 :
    recurrence5Scalar1Left.coeff 329 =
      (((((126503213888170250538553284129385953131405346582055303 * 10 ^ 70 +
        4261800603540364278850862028618285485349316829712075133364088564899615) * 10 ^ 70 +
        9610326224588985118291118772922418522591582444483794090179674449579895) * 10 ^ 70 +
        9583140730431717228681709035302633893319033961971929138490978325727746) * 10 ^ 70 +
        4545950440970170458741819715586910764936158351311132023766033833484493) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 330 = 157 +
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
    rw [show 45 = 6 +
      39 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_329_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Left_coeff_329_suffix_zero]
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
