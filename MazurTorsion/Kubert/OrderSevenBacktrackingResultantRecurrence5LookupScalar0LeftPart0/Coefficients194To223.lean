/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupLeadingSquare
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupA0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupScalar0LeftPart0Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 5 lookup certificate: Scalar0Left coefficient convolution

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
  recurrence5A0_coeff_0
  recurrence5A0_coeff_1
  recurrence5A0_coeff_2
  recurrence5A0_coeff_3
  recurrence5A0_coeff_4
  recurrence5A0_coeff_5
  recurrence5A0_coeff_6
  recurrence5A0_coeff_7
  recurrence5A0_coeff_8
  recurrence5A0_coeff_9
  recurrence5A0_coeff_10
  recurrence5A0_coeff_11
  recurrence5A0_coeff_12
  recurrence5A0_coeff_13
  recurrence5A0_coeff_14
  recurrence5A0_coeff_15
  recurrence5A0_coeff_16
  recurrence5A0_coeff_17
  recurrence5A0_coeff_18
  recurrence5A0_coeff_19
  recurrence5A0_coeff_20
  recurrence5A0_coeff_21
  recurrence5A0_coeff_22
  recurrence5A0_coeff_23
  recurrence5A0_coeff_24
  recurrence5A0_coeff_25
  recurrence5A0_coeff_26
  recurrence5A0_coeff_27
  recurrence5A0_coeff_28

attribute [local simp]
  recurrence5A0_coeff_29
  recurrence5A0_coeff_30
  recurrence5A0_coeff_31
  recurrence5A0_coeff_32
  recurrence5A0_coeff_33
  recurrence5A0_coeff_34
  recurrence5A0_coeff_35
  recurrence5A0_coeff_36
  recurrence5A0_coeff_37
  recurrence5A0_coeff_38
  recurrence5A0_coeff_39
  recurrence5A0_coeff_40
  recurrence5A0_coeff_41
  recurrence5A0_coeff_42
  recurrence5A0_coeff_43
  recurrence5A0_coeff_44
  recurrence5A0_coeff_45
  recurrence5A0_coeff_46
  recurrence5A0_coeff_47
  recurrence5A0_coeff_48
  recurrence5A0_coeff_49
  recurrence5A0_coeff_50
  recurrence5A0_coeff_51
  recurrence5A0_coeff_52
  recurrence5A0_coeff_53
  recurrence5A0_coeff_54
  recurrence5A0_coeff_55
  recurrence5A0_coeff_56
  recurrence5A0_coeff_57
  recurrence5A0_coeff_58
  recurrence5A0_coeff_59
  recurrence5A0_coeff_60
  recurrence5A0_coeff_61
  recurrence5A0_coeff_62
  recurrence5A0_coeff_63
  recurrence5A0_coeff_64
  recurrence5A0_coeff_65
  recurrence5A0_coeff_66
  recurrence5A0_coeff_67
  recurrence5A0_coeff_68
  recurrence5A0_coeff_69
  recurrence5A0_coeff_70
  recurrence5A0_coeff_71
  recurrence5A0_coeff_72
  recurrence5A0_coeff_73
  recurrence5A0_coeff_74
  recurrence5A0_coeff_75
  recurrence5A0_coeff_76
  recurrence5A0_coeff_77
  recurrence5A0_coeff_78
  recurrence5A0_coeff_79
  recurrence5A0_coeff_80
  recurrence5A0_coeff_81
  recurrence5A0_coeff_82
  recurrence5A0_coeff_83
  recurrence5A0_coeff_84
  recurrence5A0_coeff_85
  recurrence5A0_coeff_86
  recurrence5A0_coeff_87
  recurrence5A0_coeff_88
  recurrence5A0_coeff_89
  recurrence5A0_coeff_90
  recurrence5A0_coeff_91
  recurrence5A0_coeff_92

attribute [local simp]
  recurrence5A0_coeff_93
  recurrence5A0_coeff_94
  recurrence5A0_coeff_95
  recurrence5A0_coeff_96
  recurrence5A0_coeff_97
  recurrence5A0_coeff_98
  recurrence5A0_coeff_99
  recurrence5A0_coeff_100
  recurrence5A0_coeff_101
  recurrence5A0_coeff_102
  recurrence5A0_coeff_103
  recurrence5A0_coeff_104
  recurrence5A0_coeff_105
  recurrence5A0_coeff_106
  recurrence5A0_coeff_107
  recurrence5A0_coeff_108
  recurrence5A0_coeff_109
  recurrence5A0_coeff_110
  recurrence5A0_coeff_111
  recurrence5A0_coeff_112
  recurrence5A0_coeff_113
  recurrence5A0_coeff_114
  recurrence5A0_coeff_115
  recurrence5A0_coeff_116
  recurrence5A0_coeff_117
  recurrence5A0_coeff_118
  recurrence5A0_coeff_119
  recurrence5A0_coeff_120
  recurrence5A0_coeff_121
  recurrence5A0_coeff_122
  recurrence5A0_coeff_123
  recurrence5A0_coeff_124
  recurrence5A0_coeff_125
  recurrence5A0_coeff_126
  recurrence5A0_coeff_127
  recurrence5A0_coeff_128
  recurrence5A0_coeff_129
  recurrence5A0_coeff_130
  recurrence5A0_coeff_131
  recurrence5A0_coeff_132
  recurrence5A0_coeff_133
  recurrence5A0_coeff_134
  recurrence5A0_coeff_135
  recurrence5A0_coeff_136
  recurrence5A0_coeff_137
  recurrence5A0_coeff_138
  recurrence5A0_coeff_139
  recurrence5A0_coeff_140
  recurrence5A0_coeff_141
  recurrence5A0_coeff_142
  recurrence5A0_coeff_143
  recurrence5A0_coeff_144
  recurrence5A0_coeff_145
  recurrence5A0_coeff_146
  recurrence5A0_coeff_147
  recurrence5A0_coeff_148
  recurrence5A0_coeff_149
  recurrence5A0_coeff_150
  recurrence5A0_coeff_151
  recurrence5A0_coeff_152
  recurrence5A0_coeff_153
  recurrence5A0_coeff_154
  recurrence5A0_coeff_155
  recurrence5A0_coeff_156

attribute [local simp]
  recurrence5A0_coeff_157
  recurrence5A0_coeff_158
  recurrence5A0_coeff_159
  recurrence5A0_coeff_160
  recurrence5A0_coeff_161
  recurrence5A0_coeff_162
  recurrence5A0_coeff_163
  recurrence5A0_coeff_164
  recurrence5A0_coeff_165
  recurrence5A0_coeff_166
  recurrence5A0_coeff_167
  recurrence5A0_coeff_168
  recurrence5A0_coeff_169
  recurrence5A0_coeff_170
  recurrence5A0_coeff_171
  recurrence5A0_coeff_172
  recurrence5A0_coeff_173
  recurrence5A0_coeff_174
  recurrence5A0_coeff_175
  recurrence5A0_coeff_176

private theorem recurrence5Scalar0Left_coeff_194_prefix_zero :
    (∑ x ∈ Finset.range 18,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (194 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (194 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_194 :
    recurrence5Scalar0Left.coeff 194 =
      -((((((6941735643 * 10 ^ 70 +
        8744476730558164506298741410980271845402305394518433467412490527465486) * 10 ^ 70 +
        8687277217266041326774890416535551326815516132948370032088970652229055) * 10 ^ 70 +
        3467369027496378448229557076898353963946694459623023901889764415423405) * 10 ^ 70 +
        3996633038996696750469955811159957733963874943973087495683114032681666) * 10 ^ 70 +
        4372411156580969106683005412684878321237240610159032564959249549823070) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 195 = 18 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_194_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_195_prefix_zero :
    (∑ x ∈ Finset.range 19,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (195 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (195 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_195 :
    recurrence5Scalar0Left.coeff 195 =
      ((((((9110043053 * 10 ^ 70 +
        0682204196325404065046352212059932753467849704818064734271990483543953) * 10 ^ 70 +
        2010877173530404633945963127157388526684267905364167515878195225420331) * 10 ^ 70 +
        1997455572892707871454002698721400218500650841438488716026719737216255) * 10 ^ 70 +
        8710534366932749405585411628844229482816175258879557061071520906351999) * 10 ^ 70 +
        9853334492906186396011998018216462591591899411847547922101617530742712) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 196 = 19 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_195_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_196_prefix_zero :
    (∑ x ∈ Finset.range 20,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (196 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (196 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_196 :
    recurrence5Scalar0Left.coeff 196 =
      -((((((11760717177 * 10 ^ 70 +
        2135878046271185946037850288100320051353838525756093105977338473823706) * 10 ^ 70 +
        1568001125776727356272656706932653265569553146986117073395382252573409) * 10 ^ 70 +
        1828234047194644023847324478256453151128355546943948678726935946127537) * 10 ^ 70 +
        9499305511932619117703676789758224053288349531829711832755582416695558) * 10 ^ 70 +
        7135968627466928546036169672504763076467732063957459872887210568700866) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 197 = 20 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_196_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_197_prefix_zero :
    (∑ x ∈ Finset.range 21,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (197 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (197 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_197 :
    recurrence5Scalar0Left.coeff 197 =
      ((((((14935666321 * 10 ^ 70 +
        7959815456902471537999349087859288763952126388485989587944358852789054) * 10 ^ 70 +
        8626144126334797294329864578631552484170052934861020548095799257520000) * 10 ^ 70 +
        3497829090702225786726376794167227710337681656283593797487771131911583) * 10 ^ 70 +
        8299281910164524214578153074271312283841701517424187099326331517243779) * 10 ^ 70 +
        3056144843047201878755001565003150791530621936709320856891392682630815) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 198 = 21 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_197_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_198_prefix_zero :
    (∑ x ∈ Finset.range 22,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (198 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (198 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_198 :
    recurrence5Scalar0Left.coeff 198 =
      -((((((18659886965 * 10 ^ 70 +
        0211724192436622560670516024262778221270093312876422693210987785407271) * 10 ^ 70 +
        9687094799351272257718755282633354886928302496710743523825269775546278) * 10 ^ 70 +
        8726556018913509917447702323958487806684205489084352356935693108557901) * 10 ^ 70 +
        9256403420841556635204103800990232402339053321425887958850345940372768) * 10 ^ 70 +
        8964391261714941463910854188268467172657641195820708619761062413383905) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 199 = 22 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_198_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_199_prefix_zero :
    (∑ x ∈ Finset.range 23,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (199 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (199 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_199 :
    recurrence5Scalar0Left.coeff 199 =
      ((((((22935223927 * 10 ^ 70 +
        1494614876618691695243561570313383599210861357953763175000996237235294) * 10 ^ 70 +
        6610559208339229382352282356290994107647303701447656170154474300058051) * 10 ^ 70 +
        5648814977236905837888165295464610503644911397528140424668704753686710) * 10 ^ 70 +
        4342743380095676319352544154416747328624386924527906181611688205681656) * 10 ^ 70 +
        5139650733312199102226803249844849887603755774165658337783640088035902) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 200 = 23 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_199_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_200_prefix_zero :
    (∑ x ∈ Finset.range 24,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (200 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (200 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_200 :
    recurrence5Scalar0Left.coeff 200 =
      -((((((27734620861 * 10 ^ 70 +
        8439273704825239587005531508848325307915392949226027274910643156564006) * 10 ^ 70 +
        8705849084986148313817469177439769364203369230639197142483965079571300) * 10 ^ 70 +
        0921051229494229526382433677689164688733530881438318189639112715792754) * 10 ^ 70 +
        5390821985499349665276583394454448364924501912386267970009033978521437) * 10 ^ 70 +
        2649747898927491954962395336768362428124056995765801856887760337922840) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 201 = 24 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_200_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_201_prefix_zero :
    (∑ x ∈ Finset.range 25,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (201 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (201 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_201 :
    recurrence5Scalar0Left.coeff 201 =
      ((((((32997585485 * 10 ^ 70 +
        4302359328641358793499029366252043773032628957520324413146461957804106) * 10 ^ 70 +
        0625799808357166592184882187123815634019168386378379504641771914274523) * 10 ^ 70 +
        1333972184502866284971048879829275846972969919033911743363025297454699) * 10 ^ 70 +
        2539415946510284647297683895361502736860235081896994194083521950464067) * 10 ^ 70 +
        0131830741399568285628521957648554331426854795580201504581756674103901) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 202 = 25 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_201_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_202_prefix_zero :
    (∑ x ∈ Finset.range 26,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (202 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (202 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_202 :
    recurrence5Scalar0Left.coeff 202 =
      -((((((38627609967 * 10 ^ 70 +
        3347474621926277492867051207289626165554354840814987208370888309157276) * 10 ^ 70 +
        4370964932345819373639854686465320419102668465665035776131462273407163) * 10 ^ 70 +
        6604466246018719082227538417554879713125133228922652033864314197408583) * 10 ^ 70 +
        5177319407071373300130247863852855728283258415911782131447705609374603) * 10 ^ 70 +
        7073555291444134432948515219523731688012982216925156623953958776581160) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 203 = 26 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_202_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_203_prefix_zero :
    (∑ x ∈ Finset.range 27,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (203 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (203 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_203 :
    recurrence5Scalar0Left.coeff 203 =
      ((((((44492203845 * 10 ^ 70 +
        2851507673667232974070110094013098578942048615994584986081783798972686) * 10 ^ 70 +
        8017011910053790464358868151349918537178161613479989736592373329146310) * 10 ^ 70 +
        6965433611930571049386802900335635571363832947549444986827446692987402) * 10 ^ 70 +
        2254628744145294255801761392822943772155488834889512654240506472369769) * 10 ^ 70 +
        2707038993171487599949936916893610336116728005108022860572630106505398) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 204 = 27 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_203_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_204_prefix_zero :
    (∑ x ∈ Finset.range 28,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (204 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (204 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_204 :
    recurrence5Scalar0Left.coeff 204 =
      -((((((50426007377 * 10 ^ 70 +
        2045765329765582558748982378219445052298661886259783107621909987727652) * 10 ^ 70 +
        1195264705989964597597717956374674370106697263168234999321801611574784) * 10 ^ 70 +
        7061440403432116353670118356682998739073565873633330565283729519187225) * 10 ^ 70 +
        9386798694354208615531275639375822487619343694386664486046877538355852) * 10 ^ 70 +
        2328285678744816577902030772185378425916749189197074868773436306326162) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 205 = 28 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_204_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_205_prefix_zero :
    (∑ x ∈ Finset.range 29,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (205 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (205 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_205 :
    recurrence5Scalar0Left.coeff 205 =
      ((((((56237166782 * 10 ^ 70 +
        1074324331562988761827207666576100894179999424488437905072318135426185) * 10 ^ 70 +
        5573296561224643042161937974023313993593516046318019037697730072692637) * 10 ^ 70 +
        1682178800664291296376350534024051256846128474034402858757663246860659) * 10 ^ 70 +
        3398120694693308664348570788565944777314178447944760956368585613871756) * 10 ^ 70 +
        9005427153129033577199932267640749124813256802323812291533812883103663) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 206 = 29 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_205_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_206_prefix_zero :
    (∑ x ∈ Finset.range 30,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (206 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (206 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_206 :
    recurrence5Scalar0Left.coeff 206 =
      -((((((61716796718 * 10 ^ 70 +
        7749794586608532458475888342775844543995717947951910394601322959818081) * 10 ^ 70 +
        6345856486293768063107870161134167087485261628667679616589599839349292) * 10 ^ 70 +
        8924065093567198262009999821702180648898063961880147403569379795988285) * 10 ^ 70 +
        7797539922335414092484694534252138691171556071293840204924756581881648) * 10 ^ 70 +
        2045573903088725793547277719354056121205365886662948006558277995249414) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 207 = 30 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_206_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_207_prefix_zero :
    (∑ x ∈ Finset.range 31,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (207 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (207 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_207 :
    recurrence5Scalar0Left.coeff 207 =
      ((((((66650972816 * 10 ^ 70 +
        9279922038128126517666349725520832774445735283020226119830630979517086) * 10 ^ 70 +
        3978150042339922434514538333131187413206578306146524798750793836643199) * 10 ^ 70 +
        7989685767058250920183302432742257671574311529561290451769691432310643) * 10 ^ 70 +
        9208392542863180538324984559130528773694981600809363906213658741913362) * 10 ^ 70 +
        1018883642178104948031976727879335502829077712569554410556694105039931) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 208 = 31 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_207_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_208_prefix_zero :
    (∑ x ∈ Finset.range 32,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (208 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (208 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_208 :
    recurrence5Scalar0Left.coeff 208 =
      -((((((70834341564 * 10 ^ 70 +
        6232366476165067535968792698798679468977135687251575434218052502675204) * 10 ^ 70 +
        9758668768843868291472121842839473528720192843880111532708204934248974) * 10 ^ 70 +
        2845692835291433077291692391784622631275539267636077768685932886116070) * 10 ^ 70 +
        1919838492700479977483348631923513131218748811251137696671110590644954) * 10 ^ 70 +
        6098013784384458210776064617974463498585960802754084939166066008672676) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 209 = 32 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_208_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_209_prefix_zero :
    (∑ x ∈ Finset.range 33,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (209 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (209 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_209 :
    recurrence5Scalar0Left.coeff 209 =
      ((((((74084161690 * 10 ^ 70 +
        6895706532353617113889939828671706706377932536628745198041442786245728) * 10 ^ 70 +
        8365742579488720551440431087497743225505449125335942750980173894691166) * 10 ^ 70 +
        7341079400752994443756096854699416060192385712284546674324807317017798) * 10 ^ 70 +
        9065071393293592266233075897690285052150572886358051002186226317096876) * 10 ^ 70 +
        5554538484536608978367734733937045264030418379709283298435407771824385) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 210 = 33 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_209_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_210_prefix_zero :
    (∑ x ∈ Finset.range 34,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (210 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (210 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_210 :
    recurrence5Scalar0Left.coeff 210 =
      -((((((76253447863 * 10 ^ 70 +
        3982752654783230900001001325629355589453225649497087808858406638471474) * 10 ^ 70 +
        9743792688486231728202664053794408394813558383784550329347196635179216) * 10 ^ 70 +
        3929010088470814709841972330810691735407125084602310567135335749332757) * 10 ^ 70 +
        8341200516792118908513260078215786080003554820552117492670287426017869) * 10 ^ 70 +
        4263499241807812805493941619549615135238699381190804367859057040977676) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 211 = 34 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_210_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_211_prefix_zero :
    (∑ x ∈ Finset.range 35,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (211 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (211 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_211 :
    recurrence5Scalar0Left.coeff 211 =
      ((((((77241904624 * 10 ^ 70 +
        2834804838043131651072025333169821240288235266233761318885085124851104) * 10 ^ 70 +
        9566575818166949750017848023764903250681405921480441740158800638718794) * 10 ^ 70 +
        2210529465958986066864604491784124350628707042713351103268492590983415) * 10 ^ 70 +
        5242329863308509369691737481252630544596190461393992591993458781946465) * 10 ^ 70 +
        1918786652241679309218437340864091318328710221221922159570679672523678) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 212 = 35 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_211_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_212_prefix_zero :
    (∑ x ∈ Finset.range 36,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (212 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (212 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_212 :
    recurrence5Scalar0Left.coeff 212 =
      -((((((77003523038 * 10 ^ 70 +
        8705553017792570064357307391095464785233350408687545448942554985937615) * 10 ^ 70 +
        1460934334202648061557893073629363406917446409359866994178354316656399) * 10 ^ 70 +
        1160752656805953111184187265905135647574550194384717333087614580895549) * 10 ^ 70 +
        5613427733654993223125321919892543988595518419029353385534667128844078) * 10 ^ 70 +
        8739994694684027723640537488607400966140056126716140983531012761234746) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 213 = 36 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_212_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_213_prefix_zero :
    (∑ x ∈ Finset.range 37,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (213 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (213 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_213 :
    recurrence5Scalar0Left.coeff 213 =
      ((((((75550045577 * 10 ^ 70 +
        6430507260122912281190333019079410633122900121003702412024687141382539) * 10 ^ 70 +
        2079053746014520682016800897499239079971342092870185613394770125151530) * 10 ^ 70 +
        8669838947345609784228476750226700863864106939902043180025928699925715) * 10 ^ 70 +
        6650934217042080410821337473159904090942306371332973455248072915612316) * 10 ^ 70 +
        8884741108929105439355844393068420036428720929922926053204015743512863) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 214 = 37 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_213_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_214_prefix_zero :
    (∑ x ∈ Finset.range 38,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (214 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (214 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_214 :
    recurrence5Scalar0Left.coeff 214 =
      -((((((72949943453 * 10 ^ 70 +
        5939576249526072106447159112248277978510779199516185312638864514695102) * 10 ^ 70 +
        4688718406494643003064786000057374221856661139106925381913346873703201) * 10 ^ 70 +
        6725489067630430733325702574090404898436204825213739892038253631144388) * 10 ^ 70 +
        9740183047970439174335621013846833624643411170753824999391844992793497) * 10 ^ 70 +
        1190922396077831987745473549279709320488369448023460058030994557052013) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 215 = 38 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_214_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_215_prefix_zero :
    (∑ x ∈ Finset.range 39,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (215 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (215 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_215 :
    recurrence5Scalar0Left.coeff 215 =
      ((((((69323035209 * 10 ^ 70 +
        2307611170601081769306835177361605157521458904903262712376704559829928) * 10 ^ 70 +
        8811347421164128981399563077234367363159754381112962715352607737142850) * 10 ^ 70 +
        6599614975951538996311250118358899443157168237846890600825656671712771) * 10 ^ 70 +
        9176393685292492117042520502182400528486004809493528748440568463980663) * 10 ^ 70 +
        0154370089145131306002058298067355148229891322664648104110201724776993) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 216 = 39 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_215_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_216_prefix_zero :
    (∑ x ∈ Finset.range 40,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (216 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (216 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_216 :
    recurrence5Scalar0Left.coeff 216 =
      -((((((64831338875 * 10 ^ 70 +
        2667639461836342054431156570246796872908732815785633123319826633520493) * 10 ^ 70 +
        3567684462702842573288498719273306289829999592359606481629654381373980) * 10 ^ 70 +
        0588052035285658844001873383666099345436932968821069149075855413056689) * 10 ^ 70 +
        5854582420020063161625025112998232148272535395484328203935386604667256) * 10 ^ 70 +
        9809356283386630017916861015046610063260851704964597820329627120560073) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 217 = 40 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_216_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_217_prefix_zero :
    (∑ x ∈ Finset.range 41,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (217 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (217 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_217 :
    recurrence5Scalar0Left.coeff 217 =
      ((((((59667129797 * 10 ^ 70 +
        8968541769121682615997422694957236329625780080497562548978948061502332) * 10 ^ 70 +
        1404947239797324692001726516082693432979824147121992398205973712713708) * 10 ^ 70 +
        0171983964307525242375086193865796471467927248927837188198444127200060) * 10 ^ 70 +
        9747168398935224713046972378931743287342873611953585406689362791519680) * 10 ^ 70 +
        2712979739245274819040192036143481200832704679140612317378892622382250) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 218 = 41 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_217_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_218_prefix_zero :
    (∑ x ∈ Finset.range 42,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (218 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (218 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_218 :
    recurrence5Scalar0Left.coeff 218 =
      -((((((54039423978 * 10 ^ 70 +
        3652133073554579165688498645873680532294522974599047486823944715617318) * 10 ^ 70 +
        2987781734374725260711031123751550263044704734360012839842457276379901) * 10 ^ 70 +
        3326490480852849358901487942132926315476509589629342101067503218998941) * 10 ^ 70 +
        3775558777264665402170647793804885165941376336634802874288946427953292) * 10 ^ 70 +
        6875946110826495898856863989231468025384872179128936310376889218260194) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 219 = 42 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_218_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_219_prefix_zero :
    (∑ x ∈ Finset.range 43,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (219 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (219 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_219 :
    recurrence5Scalar0Left.coeff 219 =
      ((((((48160195995 * 10 ^ 70 +
        6303698398734809105423085779405669692172428606288334223118754025856156) * 10 ^ 70 +
        2480083171317558788008221550349708808763389697163631745267034565925577) * 10 ^ 70 +
        8126469666263487310337289504680297210543459061013601533988760329454944) * 10 ^ 70 +
        3771171800939357968347002419058823872220409495691699849943883559510340) * 10 ^ 70 +
        0699332824353198926302051455355780656299046924782295363915451402930080) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 220 = 43 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_219_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_220_prefix_zero :
    (∑ x ∈ Finset.range 44,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (220 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (220 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_220 :
    recurrence5Scalar0Left.coeff 220 =
      -((((((42231569697 * 10 ^ 70 +
        5274533972935411898496770384636082020190833421296462537130175152761054) * 10 ^ 70 +
        4315962777557141457879489998210255385293808250136994130275326886478231) * 10 ^ 70 +
        6453345717901519077842622436274299716431202415561873006124898019560711) * 10 ^ 70 +
        6243691072739360423491514912836573079410930088043295736476507568726936) * 10 ^ 70 +
        2302630229507912408660384174696486837580298176197601778058889690370792) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 221 = 44 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_220_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_221_prefix_zero :
    (∑ x ∈ Finset.range 45,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (221 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (221 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_221 :
    recurrence5Scalar0Left.coeff 221 =
      ((((((36435010704 * 10 ^ 70 +
        5087515206348462125585633151666264762658562261290713544183622953553581) * 10 ^ 70 +
        5608609058977815741737156000770243072931998266094340415347653066898234) * 10 ^ 70 +
        0876726405331233588122247655294192095776296385491366200898239993578698) * 10 ^ 70 +
        4752747369906144158356167308840634843141527837386892001444430945465594) * 10 ^ 70 +
        1414344832815337135065819554170512435737456254270302339806497457898335) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 222 = 45 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_221_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_222_prefix_zero :
    (∑ x ∈ Finset.range 46,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (222 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (222 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_222 :
    recurrence5Scalar0Left.coeff 222 =
      -((((((30923242267 * 10 ^ 70 +
        7653526160625891280412906313957388399339606161079373695055017824295107) * 10 ^ 70 +
        7902002304432359361170790577319494654243807223070339165586690970383762) * 10 ^ 70 +
        7086409745613946880447808976248558083552777824207599588417725267259945) * 10 ^ 70 +
        9478019924300744333751503978507951862600351406036707847232863830822042) * 10 ^ 70 +
        8762789965872750871643393532315436309483772657246249843231161588021460) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 223 = 46 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_222_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_223_prefix_zero :
    (∑ x ∈ Finset.range 47,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (223 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (223 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_223 :
    recurrence5Scalar0Left.coeff 223 =
      ((((((25815250076 * 10 ^ 70 +
        6963473957531659573989379877134712240212918980634055865469331264865521) * 10 ^ 70 +
        1403158856414211053953323907870693035557116488737447463714567677778712) * 10 ^ 70 +
        1343038176846423012620155741736766828160342050669078007059502555595925) * 10 ^ 70 +
        4689364639275875265480393903723477767406577938632777226719754269817387) * 10 ^ 70 +
        3729352142108638166983071964733045604533295772427115261976571162111381) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 224 = 47 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_223_prefix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
