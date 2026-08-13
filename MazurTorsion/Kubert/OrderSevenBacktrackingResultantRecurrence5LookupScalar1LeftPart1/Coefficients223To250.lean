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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
