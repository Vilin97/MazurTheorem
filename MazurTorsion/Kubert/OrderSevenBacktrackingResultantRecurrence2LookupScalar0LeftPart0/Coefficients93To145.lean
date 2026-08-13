/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupLeadingSquare
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupA0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar0LeftPart0Simp
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

theorem recurrence2Scalar0Left_coeff_93 :
    recurrence2Scalar0Left.coeff 93 =
      (((12205612 * 10 ^ 70 +
        9670116791929731697644254387109676019243663323458484580952181153422869) * 10 ^ 70 +
        2293759075133267521865662239170739460100983797025184431244606819043458) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 94 = 0 +
    94 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 94 = 32 +
      62 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 62 = 32 +
      30 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 30 = 30 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence2Scalar0Left_coeff_94 :
    recurrence2Scalar0Left.coeff 94 =
      -(((58629733 * 10 ^ 70 +
        3358134333763208146658044306507251376159266989670700522597792510626056) * 10 ^ 70 +
        6901007811280741545470829534595994603263016593136718167942944256873998) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 95 = 0 +
    95 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 31 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence2Scalar0Left_coeff_95 :
    recurrence2Scalar0Left.coeff 95 =
      (((270312635 * 10 ^ 70 +
        2264165363497700917953284815954672678838832622636013701188368159313175) * 10 ^ 70 +
        9540582627490253677559352734172958384675179633105917547023915204870467) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 96 = 0 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence2Scalar0Left_coeff_96 :
    recurrence2Scalar0Left.coeff 96 =
      -(((1195326738 * 10 ^ 70 +
        7960124760868854505978904808613554618262456280507439289108291209844993) * 10 ^ 70 +
        6637891238379628558773654018766476231359186045676880324224062680056105) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 97 = 0 +
    97 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 97 = 32 +
      65 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 65 = 32 +
      33 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 33 = 32 +
      1 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 1 = 1 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence2Scalar0Left_coeff_97 :
    recurrence2Scalar0Left.coeff 97 =
      (((5063522450 * 10 ^ 70 +
        4251204049483655335089796146860111511184132961658020673064632818449632) * 10 ^ 70 +
        9238827016628107063856338641599786080221785304374189037209050854373190) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 98 = 0 +
    98 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 98 = 32 +
      66 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 66 = 32 +
      34 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 34 = 32 +
      2 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 2 = 2 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence2Scalar0Left_coeff_98 :
    recurrence2Scalar0Left.coeff 98 =
      -(((20500712943 * 10 ^ 70 +
        1059218421732417412925294048872939816504219278021281875376587676875613) * 10 ^ 70 +
        9089156305022978654962126252582617508223733851039475622874182515907099) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 99 = 0 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence2Scalar0Left_coeff_99 :
    recurrence2Scalar0Left.coeff 99 =
      (((78997526222 * 10 ^ 70 +
        8804536151009119535187574173112778108596570864851383928390907192254144) * 10 ^ 70 +
        0480617534341330549576294131902654147031829999905588747619804659586850) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 100 = 0 +
    100 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 100 = 32 +
      68 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 68 = 32 +
      36 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 36 = 32 +
      4 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence2Scalar0Left_coeff_100 :
    recurrence2Scalar0Left.coeff 100 =
      -(((287693237043 * 10 ^ 70 +
        1018584161841836342006634054484339791737540371353978942290011363934699) * 10 ^ 70 +
        4553581973010770401288212502640948716837016765759833223602366714683498) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 101 = 0 +
    101 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 32 +
      5 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 5 = 5 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence2Scalar0Left_coeff_101 :
    recurrence2Scalar0Left.coeff 101 =
      (((979354473627 * 10 ^ 70 +
        6253329224810187741184148352392264037602363838892939377475712303877635) * 10 ^ 70 +
        4111629774550645668874325251930905699486578340371759264388327644827507) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 102 = 0 +
    102 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 102 = 32 +
      70 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 70 = 32 +
      38 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 38 = 32 +
      6 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 6 = 6 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence2Scalar0Left_coeff_102 :
    recurrence2Scalar0Left.coeff 102 =
      -(((3063945441958 * 10 ^ 70 +
        7543961397064606793900702520373183533362528460453638626118540149890068) * 10 ^ 70 +
        8359402432152104929111316440511569417711850284270761542505192134783216) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 103 = 0 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 32 +
      39 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 39 = 32 +
      7 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence2Scalar0Left_coeff_103 :
    recurrence2Scalar0Left.coeff 103 =
      (((8561653422442 * 10 ^ 70 +
        8819692878683502327880187960040610580119269897721226569450509202431058) * 10 ^ 70 +
        0476343402256606209881297726780694363294071277024689107549252713349412) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 104 = 0 +
    104 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 104 = 32 +
      72 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 72 = 32 +
      40 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 40 = 32 +
      8 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 8 = 8 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence2Scalar0Left_coeff_104 :
    recurrence2Scalar0Left.coeff 104 =
      -(((20096920369312 * 10 ^ 70 +
        2880642967156647296221169592193151937197761824455695546420795420679901) * 10 ^ 70 +
        7635130905650339150271762261915731320333765037716710468860124331685828) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 105 = 0 +
    105 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 105 = 32 +
      73 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 73 = 32 +
      41 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 41 = 32 +
      9 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 9 = 9 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence2Scalar0Left_coeff_105 :
    recurrence2Scalar0Left.coeff 105 =
      (((31926469249669 * 10 ^ 70 +
        6199920246413393775645870072186089323778267617765451890747003388410524) * 10 ^ 70 +
        7333850355202506104911770358580409884544063440622988480780290711405019) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 106 = 0 +
    106 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 106 = 32 +
      74 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 74 = 32 +
      42 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 42 = 32 +
      10 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 10 = 10 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence2Scalar0Left_coeff_106 :
    recurrence2Scalar0Left.coeff 106 =
      (((23641315433917 * 10 ^ 70 +
        7229667721130119065298212811259945643697650071083140264460078595182349) * 10 ^ 70 +
        0576700126731498751172734569602333006214073653170259031903563881081007) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 107 = 0 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 32 +
      43 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 43 = 32 +
      11 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 11 = 11 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence2Scalar0Left_coeff_107 :
    recurrence2Scalar0Left.coeff 107 =
      -(((544464799095724 * 10 ^ 70 +
        3339359326782960119192408889148696863513974945725742993720569280675698) * 10 ^ 70 +
        8977396977538399382018591712908122208488908536814710735415036859222271) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 108 = 0 +
    108 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 108 = 32 +
      76 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 76 = 32 +
      44 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 44 = 32 +
      12 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 12 = 12 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence2Scalar0Left_coeff_108 :
    recurrence2Scalar0Left.coeff 108 =
      (((3521790626057322 * 10 ^ 70 +
        8912624823655654432058802260786918546061011351858159257778595719427703) * 10 ^ 70 +
        9473564624575710431875031691648539079589847724331941973526663704079938) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 109 = 0 +
    109 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  order_seven_normalize_coefficient_sum

theorem recurrence2Scalar0Left_coeff_109 :
    recurrence2Scalar0Left.coeff 109 =
      -(((18032217314329734 * 10 ^ 70 +
        2312927873785201209387876132266132926116252789969325311988319721547848) * 10 ^ 70 +
        1316873881957335286341487398431330662811243400853469939941798093779282) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 110 = 0 +
    110 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 110 = 32 +
      78 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 78 = 32 +
      46 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 46 = 32 +
      14 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence2Scalar0Left_coeff_110 :
    recurrence2Scalar0Left.coeff 110 =
      (((80626596571898484 * 10 ^ 70 +
        7083887902105867934680467160022436312600685466600104570931838535858512) * 10 ^ 70 +
        8105880420339933749265183982850314815507269807802901776685458338793550) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 111 = 0 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 32 +
      47 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 47 = 32 +
      15 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence2Scalar0Left_coeff_111 :
    recurrence2Scalar0Left.coeff 111 =
      -(((310749874428073668 * 10 ^ 70 +
        6880145978239716911564230719005348049106369091317772893625601698678542) * 10 ^ 70 +
        2584517826040188336505726745776581424502091382493502674863843838969079) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 112 = 0 +
    112 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 112 = 32 +
      80 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 80 = 32 +
      48 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 48 = 32 +
      16 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 16 = 16 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence2Scalar0Left_coeff_112 :
    recurrence2Scalar0Left.coeff 112 =
      (((961903079911194027 * 10 ^ 70 +
        6559225285997392101474622009211143680656491286684995050500735999651157) * 10 ^ 70 +
        3338459165444407666899947274915459986734235154452408597168889446700583) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 113 = 0 +
    113 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  order_seven_normalize_coefficient_sum

theorem recurrence2Scalar0Left_coeff_113 :
    recurrence2Scalar0Left.coeff 113 =
      -(((1950796822556066330 * 10 ^ 70 +
        7416540750194542578773170709175746519427091825432458876625818605954469) * 10 ^ 70 +
        5976817068461706273123481064270982001169940423665133049050179921902341) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 114 = 0 +
    114 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence2Scalar0Left_coeff_114 :
    recurrence2Scalar0Left.coeff 114 =
      -(((175101519447809920 * 10 ^ 70 +
        9714814421780521237809429608205108226191001209058181764567741310200028) * 10 ^ 70 +
        6717665724680457633457746823436717343707845643774902114599933212082216) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 115 = 0 +
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
  order_seven_normalize_coefficient_sum

theorem recurrence2Scalar0Left_coeff_115 :
    recurrence2Scalar0Left.coeff 115 =
      (((19089177561245600513 * 10 ^ 70 +
        2425715651570664856175407923722940849292717384232751991983193405251749) * 10 ^ 70 +
        1211989410066549282519496059660383893112219933247886351849409189822603) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 116 = 0 +
    116 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 116 = 32 +
      84 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 84 = 32 +
      52 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 52 = 32 +
      20 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 20 = 20 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence2Scalar0Left_coeff_116 :
    recurrence2Scalar0Left.coeff 116 =
      -(((55995518839608095981 * 10 ^ 70 +
        8920076610309924083669363656779340581534561979531393687959230238047207) * 10 ^ 70 +
        5722844571194959952599303876979988540684555763838442879063668214044695) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 117 = 0 +
    117 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 117 = 32 +
      85 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence2Scalar0Left_coeff_117 :
    recurrence2Scalar0Left.coeff 117 =
      -(((172000269050581851638 * 10 ^ 70 +
        2420211508507341729658738711600605769496873078618814042718043185957979) * 10 ^ 70 +
        3816632384396901907350021867210977274008954060825053262965904409250869) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 118 = 0 +
    118 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 22 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence2Scalar0Left_coeff_118 :
    recurrence2Scalar0Left.coeff 118 =
      (((2411368682396605374940 * 10 ^ 70 +
        2750808452696358638945387534355574880786457489790359210818875653295612) * 10 ^ 70 +
        7976364394935505149493924770214971560087343951616086766324819214876610) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 119 = 0 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_119_prefix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (119 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (119 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_119 :
    recurrence2Scalar0Left.coeff 119 =
      -(((11906375492587163228945 * 10 ^ 70 +
        2927839752077313424294169782367526144767258980930089188416614331518979) * 10 ^ 70 +
        3752853821249722792691756566880318098392099469280504845175469526851250) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 120 = 1 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_119_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_120_prefix_zero :
    (∑ x ∈ Finset.range 2,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (120 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (120 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_120 :
    recurrence2Scalar0Left.coeff 120 =
      (((29023755539295809680208 * 10 ^ 70 +
        7035312521184089149573299040414442385152865120275575477666420997271343) * 10 ^ 70 +
        8408491130547892970504068786520937249136914566883549832108942630243976) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 121 = 2 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_120_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_121_prefix_zero :
    (∑ x ∈ Finset.range 3,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (121 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (121 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_121 :
    recurrence2Scalar0Left.coeff 121 =
      (((32735886580857777333210 * 10 ^ 70 +
        1291131480231658582277299473291356380781505205407253833276114425976334) * 10 ^ 70 +
        6490804552105073993932003948134628864740478028859875426994770558159791) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 122 = 3 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_121_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_122_prefix_zero :
    (∑ x ∈ Finset.range 4,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (122 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (122 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_122 :
    recurrence2Scalar0Left.coeff 122 =
      -(((690361182942019537518913 * 10 ^ 70 +
        6078456201843886635409690433126064920883855041922534078443682214585936) * 10 ^ 70 +
        5106572046658303594197359634607117306344700488302147838078784746890950) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 123 = 4 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_122_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_123_prefix_zero :
    (∑ x ∈ Finset.range 5,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (123 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (123 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_123 :
    recurrence2Scalar0Left.coeff 123 =
      (((3635677248273860589860421 * 10 ^ 70 +
        5068975055456440214461991595146012517457705070704365920330144227239350) * 10 ^ 70 +
        7771636375514123589430826814372097633105889189230948715416707703139905) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 124 = 5 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_123_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_124_prefix_zero :
    (∑ x ∈ Finset.range 6,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (124 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (124 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_124 :
    recurrence2Scalar0Left.coeff 124 =
      -(((10963563988105403197125207 * 10 ^ 70 +
        8961615835475073147219121638240670692233359210070911869589995943608921) * 10 ^ 70 +
        2718150306898755292609662817120812328488896778537777067083557117240764) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 125 = 6 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_124_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_125_prefix_zero :
    (∑ x ∈ Finset.range 7,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (125 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (125 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_125 :
    recurrence2Scalar0Left.coeff 125 =
      (((10223523821411579015326509 * 10 ^ 70 +
        7775678653997878895084668803390530757038061232798934187770702069073151) * 10 ^ 70 +
        6787719378889122562198653487448131617809188530946024734824102516507610) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 126 = 7 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_125_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_126_prefix_zero :
    (∑ x ∈ Finset.range 8,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (126 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (126 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_126 :
    recurrence2Scalar0Left.coeff 126 =
      (((96920631738774786120297494 * 10 ^ 70 +
        0742923250446499780023588566258275756944721941314162249345461879001644) * 10 ^ 70 +
        6558325247642320033368289532623452451982805985462362796089520356264862) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 127 = 8 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_126_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_127_prefix_zero :
    (∑ x ∈ Finset.range 9,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (127 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (127 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_127 :
    recurrence2Scalar0Left.coeff 127 =
      -(((676475743830521157972704149 * 10 ^ 70 +
        6166331692824650768709541792216012353209090335246883807076207189043556) * 10 ^ 70 +
        2406248411201034991959197572615408245139331983909783948107814171787160) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 128 = 9 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_127_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_128_prefix_zero :
    (∑ x ∈ Finset.range 10,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (128 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (128 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_128 :
    recurrence2Scalar0Left.coeff 128 =
      (((2441033421095542009158826567 * 10 ^ 70 +
        9268141714324754528475264329321349344922485994372689882789577419082890) * 10 ^ 70 +
        1879567035567632581222362870148587148407021272581471012208928009791954) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 129 = 10 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_128_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_129_prefix_zero :
    (∑ x ∈ Finset.range 11,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (129 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (129 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_129 :
    recurrence2Scalar0Left.coeff 129 =
      -(((5186795870966157144305992113 * 10 ^ 70 +
        4512556563885258718648643324434833687955832739902492607233501888820423) * 10 ^ 70 +
        0580170430651579462166706993362626048771775892722013078258090138798964) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 130 = 11 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_129_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_130_prefix_zero :
    (∑ x ∈ Finset.range 12,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (130 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (130 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_130 :
    recurrence2Scalar0Left.coeff 130 =
      (((3094281278228160721901721751 * 10 ^ 70 +
        6787806247404286814947943000224064520808042589178029233013299008624117) * 10 ^ 70 +
        1743903288612209439145146059401503456813205427884198733702559539987215) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 131 = 12 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_130_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_131_prefix_zero :
    (∑ x ∈ Finset.range 13,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (131 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (131 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_131 :
    recurrence2Scalar0Left.coeff 131 =
      (((26630437085927772143151533043 * 10 ^ 70 +
        3119808867885021342396966159972717758018691990821464714546142966591445) * 10 ^ 70 +
        1569488287657471584030065327680019622027321215332750404432196843678556) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 132 = 13 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_131_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_132_prefix_zero :
    (∑ x ∈ Finset.range 14,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (132 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (132 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_132 :
    recurrence2Scalar0Left.coeff 132 =
      -(((217007445332078232138566030180 * 10 ^ 70 +
        7191849465185378658304958294481281991030828373430068241350126068813833) * 10 ^ 70 +
        5980122877912020855650040812850904421593511745302439126927825653461074) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 133 = 14 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_132_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_133_prefix_zero :
    (∑ x ∈ Finset.range 15,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (133 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (133 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_133 :
    recurrence2Scalar0Left.coeff 133 =
      (((1577541970728949194200773639164 * 10 ^ 70 +
        0949890431559400484167473184206735553950648937279617221698474815034820) * 10 ^ 70 +
        5266471460836751297752342170782492365450151106481979752543860296462462) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 134 = 15 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_133_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_134_prefix_zero :
    (∑ x ∈ Finset.range 16,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (134 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (134 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_134 :
    recurrence2Scalar0Left.coeff 134 =
      -(((8999193462075021127318099102459 * 10 ^ 70 +
        0007392112895285831969350812439244140982411416863984856611095081412562) * 10 ^ 70 +
        8249787779902765938071880787633649099512548879522955559849259218581466) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 135 = 16 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_134_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_135_prefix_zero :
    (∑ x ∈ Finset.range 17,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (135 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (135 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_135 :
    recurrence2Scalar0Left.coeff 135 =
      (((30707025648391110625678023819453 * 10 ^ 70 +
        2180781788566585221402712985486164389104128941890517353806848173835899) * 10 ^ 70 +
        0697255331286531798160476062618700247659043439491248206536922678101004) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 136 = 17 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_135_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_136_prefix_zero :
    (∑ x ∈ Finset.range 18,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (136 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (136 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_136 :
    recurrence2Scalar0Left.coeff 136 =
      -(((9333909619870777461352706707700 * 10 ^ 70 +
        2801258067281038460816561931146416578858421544453009812040318648858421) * 10 ^ 70 +
        5735077289654143213401329070022240312548074146985355114462795666135229) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 137 = 18 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_136_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_137_prefix_zero :
    (∑ x ∈ Finset.range 19,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (137 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (137 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_137 :
    recurrence2Scalar0Left.coeff 137 =
      -(((527944035530545234814865235449552 * 10 ^ 70 +
        6120836030555979406607549879829454826334470267932716510460823341034590) * 10 ^ 70 +
        4800280830443109342896606475432735267907865448914519466250979014988236) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 138 = 19 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_137_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_138_prefix_zero :
    (∑ x ∈ Finset.range 20,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (138 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (138 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_138 :
    recurrence2Scalar0Left.coeff 138 =
      (((2977474759272394788166797275488473 * 10 ^ 70 +
        0331311050880913562495679696963352094007967374278016925532177932481929) * 10 ^ 70 +
        8705440620235975248036951674128648854342605876754601697338781924875443) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 139 = 20 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_138_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_139_prefix_zero :
    (∑ x ∈ Finset.range 21,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (139 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (139 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_139 :
    recurrence2Scalar0Left.coeff 139 =
      -(((6484494930879142323639836493705713 * 10 ^ 70 +
        6262588548186947603261275122603423560036252955176835928855778054315518) * 10 ^ 70 +
        9523508447195933703508268392953465527091096429473336468312066759708261) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 140 = 21 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_139_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_140_prefix_zero :
    (∑ x ∈ Finset.range 22,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (140 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (140 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_140 :
    recurrence2Scalar0Left.coeff 140 =
      -(((12399001518819038951116911447943331 * 10 ^ 70 +
        5423637290590746212575002434204384302558959184244737317369448086960381) * 10 ^ 70 +
        3272517007522258164825048308790096195064874716951719207080064362315291) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 141 = 22 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_140_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_141_prefix_zero :
    (∑ x ∈ Finset.range 23,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (141 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (141 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_141 :
    recurrence2Scalar0Left.coeff 141 =
      (((133452302894542191610879553413638346 * 10 ^ 70 +
        0024241222561539122697732862275797466872666283435555417753413362725512) * 10 ^ 70 +
        6631114002528863565461814107857030445596852716904912548542347568794305) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 142 = 23 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_141_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_142_prefix_zero :
    (∑ x ∈ Finset.range 24,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (142 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (142 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_142 :
    recurrence2Scalar0Left.coeff 142 =
      -(((339058908489567814507253570903671457 * 10 ^ 70 +
        5815187842960072397149045280837464935939313840844514707502352856139241) * 10 ^ 70 +
        5533388301498163428540494628810982745492005741190259229327482580469890) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 143 = 24 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_142_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_143_prefix_zero :
    (∑ x ∈ Finset.range 25,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (143 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (143 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_143 :
    recurrence2Scalar0Left.coeff 143 =
      -(((477575197657590189829384198623842990 * 10 ^ 70 +
        3383952509297720533958650201559836145391957326736367842941792484789685) * 10 ^ 70 +
        1912239191168239680218339509628372079516539935314550302640687018323592) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 144 = 25 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_143_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_144_prefix_zero :
    (∑ x ∈ Finset.range 26,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (144 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (144 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_144 :
    recurrence2Scalar0Left.coeff 144 =
      (((5843831692139928351044593653277594690 * 10 ^ 70 +
        9704053331288304180102261650384301529292331679321134504236320886146411) * 10 ^ 70 +
        8582937731521692644192916364757085626950071595500690720346308875691466) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 145 = 26 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_144_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_145_prefix_zero :
    (∑ x ∈ Finset.range 27,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (145 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (145 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_145 :
    recurrence2Scalar0Left.coeff 145 =
      -(((12945351499138117091221413881333513271 * 10 ^ 70 +
        5200057910493800692412437921049342146630378380495684665096198857752932) * 10 ^ 70 +
        2889852332887959814790309803608068860656172545565971307812915659240443) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 146 = 27 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_145_prefix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
