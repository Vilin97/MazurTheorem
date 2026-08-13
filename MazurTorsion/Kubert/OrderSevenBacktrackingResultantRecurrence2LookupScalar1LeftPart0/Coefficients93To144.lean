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

theorem recurrence2Scalar1Left_coeff_93 :
    recurrence2Scalar1Left.coeff 93 =
      (((58827786 * 10 ^ 70 +
        4432406129800774748573646224325706075461829078396926021275319512776582) * 10 ^ 70 +
        8906252271144102999124906700809315502248828714058450203850278218065695) : ℚ) := by
  unfold recurrence2Scalar1Left
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

theorem recurrence2Scalar1Left_coeff_94 :
    recurrence2Scalar1Left.coeff 94 =
      -(((268974026 * 10 ^ 70 +
        7794696292268061596290829201028004683688670117923165775068359629197602) * 10 ^ 70 +
        1320700101329068814843826020479095928194307759561248941928147062622957) : ℚ) := by
  unfold recurrence2Scalar1Left
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

theorem recurrence2Scalar1Left_coeff_95 :
    recurrence2Scalar1Left.coeff 95 =
      (((1179356278 * 10 ^ 70 +
        0832246569275813152270076524823531042593473324199488443272691540874834) * 10 ^ 70 +
        7521132714772023173653439041424259868083939760695358050437241238184007) : ℚ) := by
  unfold recurrence2Scalar1Left
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

theorem recurrence2Scalar1Left_coeff_96 :
    recurrence2Scalar1Left.coeff 96 =
      -(((4951589539 * 10 ^ 70 +
        5063573083873226737676670180735184224253718721123490567511676525606642) * 10 ^ 70 +
        4772530887887269219957720565354307039678583124351501391359479393507041) : ℚ) := by
  unfold recurrence2Scalar1Left
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

theorem recurrence2Scalar1Left_coeff_97 :
    recurrence2Scalar1Left.coeff 97 =
      (((19856243849 * 10 ^ 70 +
        3610016663755781949512429201338684598725890351843090320101442835809032) * 10 ^ 70 +
        2900276801078865547528500218284276599670917825088585990981926553059310) : ℚ) := by
  unfold recurrence2Scalar1Left
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

theorem recurrence2Scalar1Left_coeff_98 :
    recurrence2Scalar1Left.coeff 98 =
      -(((75715641249 * 10 ^ 70 +
        9502978594245802834804203255843643843936254725800898257557304926640044) * 10 ^ 70 +
        0838922612020177368812675188114906036430977285987591804340100030020855) : ℚ) := by
  unfold recurrence2Scalar1Left
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

theorem recurrence2Scalar1Left_coeff_99 :
    recurrence2Scalar1Left.coeff 99 =
      (((272560292616 * 10 ^ 70 +
        3698661086247701156764393307744555336948143854358382314774428929317053) * 10 ^ 70 +
        6233796250038026575727413860472821236378019458794461095045464435084025) : ℚ) := by
  unfold recurrence2Scalar1Left
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

theorem recurrence2Scalar1Left_coeff_100 :
    recurrence2Scalar1Left.coeff 100 =
      -(((915694116826 * 10 ^ 70 +
        3665172799764213648695879602970168181571868982088690389315686044832402) * 10 ^ 70 +
        4405298452732843899826799941091108928264452060994387208142795236758342) : ℚ) := by
  unfold recurrence2Scalar1Left
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

theorem recurrence2Scalar1Left_coeff_101 :
    recurrence2Scalar1Left.coeff 101 =
      (((2818708373261 * 10 ^ 70 +
        5046714191163118772468168596516001896036883590375324459257557473389294) * 10 ^ 70 +
        7359756138577470191740645193879617058550050286139567594657599313075458) : ℚ) := by
  unfold recurrence2Scalar1Left
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

theorem recurrence2Scalar1Left_coeff_102 :
    recurrence2Scalar1Left.coeff 102 =
      -(((7690128628719 * 10 ^ 70 +
        3862913796108494628476024596423416557394652811168777304770478896726811) * 10 ^ 70 +
        7441601881734677547328058651689143891038680696783066592068566782309507) : ℚ) := by
  unfold recurrence2Scalar1Left
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

theorem recurrence2Scalar1Left_coeff_103 :
    recurrence2Scalar1Left.coeff 103 =
      (((17192412077097 * 10 ^ 70 +
        9692904328903721100704860646442652015478295485311314374887003763671042) * 10 ^ 70 +
        0140334184272964381036911811251834888806882341766108362340625646999696) : ℚ) := by
  unfold recurrence2Scalar1Left
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

theorem recurrence2Scalar1Left_coeff_104 :
    recurrence2Scalar1Left.coeff 104 =
      -(((22632705884759 * 10 ^ 70 +
        5238900286917122428342203822815680365565366464404227784808573966787417) * 10 ^ 70 +
        2060063193437826535909029155649890187734062108186934232352131679836114) : ℚ) := by
  unfold recurrence2Scalar1Left
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

theorem recurrence2Scalar1Left_coeff_105 :
    recurrence2Scalar1Left.coeff 105 =
      -(((52395636312396 * 10 ^ 70 +
        7457690939279865454142327798692615479740764916361155138233996313083275) * 10 ^ 70 +
        4557989667305692605105040160852099504521967218696893948270536028689497) : ℚ) := by
  unfold recurrence2Scalar1Left
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

theorem recurrence2Scalar1Left_coeff_106 :
    recurrence2Scalar1Left.coeff 106 =
      (((624780238039003 * 10 ^ 70 +
        5956546833549355990692783448531433269119129888785005083509333456832460) * 10 ^ 70 +
        0755623788444407903192946673895439120193280963598947668332254751254725) : ℚ) := by
  unfold recurrence2Scalar1Left
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

theorem recurrence2Scalar1Left_coeff_107 :
    recurrence2Scalar1Left.coeff 107 =
      -(((3666462208845041 * 10 ^ 70 +
        7475854423234724957197799673540926083006012805223607176862296219139504) * 10 ^ 70 +
        7952345063340440561821729317141670120995137659334324224633862273233394) : ℚ) := by
  unfold recurrence2Scalar1Left
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

theorem recurrence2Scalar1Left_coeff_108 :
    recurrence2Scalar1Left.coeff 108 =
      (((17699509765584951 * 10 ^ 70 +
        3673972515220027136150598914727182688839732888948144763848650515976917) * 10 ^ 70 +
        2161724417850701647573793848296201509011083859464713130968710872110449) : ℚ) := by
  unfold recurrence2Scalar1Left
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

theorem recurrence2Scalar1Left_coeff_109 :
    recurrence2Scalar1Left.coeff 109 =
      -(((75464422261107684 * 10 ^ 70 +
        2784835042228810060226667975219026561956895319918132674940445760266226) * 10 ^ 70 +
        2618156307766564363404816340912153288045602854696109757627612010348653) : ℚ) := by
  unfold recurrence2Scalar1Left
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

theorem recurrence2Scalar1Left_coeff_110 :
    recurrence2Scalar1Left.coeff 110 =
      (((280035898720168084 * 10 ^ 70 +
        5386235770214955657569489177197003585162502989191036734435207393076183) * 10 ^ 70 +
        8444898991458056590534924861247805274483785004292374188953190558663650) : ℚ) := by
  unfold recurrence2Scalar1Left
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

theorem recurrence2Scalar1Left_coeff_111 :
    recurrence2Scalar1Left.coeff 111 =
      -(((845481429395484670 * 10 ^ 70 +
        1615825311934108569503681796131857217430914497596182693318545047994927) * 10 ^ 70 +
        3951061268091868549067474994991041388345312953297284905612920217267154) : ℚ) := by
  unfold recurrence2Scalar1Left
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

theorem recurrence2Scalar1Left_coeff_112 :
    recurrence2Scalar1Left.coeff 112 =
      (((1724830628753702886 * 10 ^ 70 +
        0124272626654457115268226149121514988912539809133437596769169727004078) * 10 ^ 70 +
        3242918568040454618380923004871308177496674956801461977756762480378532) : ℚ) := by
  unfold recurrence2Scalar1Left
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

theorem recurrence2Scalar1Left_coeff_113 :
    recurrence2Scalar1Left.coeff 113 =
      -(((310866113768011547 * 10 ^ 70 +
        0450101378607235760365493984799974527053927345503418661978301819716674) * 10 ^ 70 +
        7680628152764502355648009444353700059929997664359899188427828772826677) : ℚ) := by
  unfold recurrence2Scalar1Left
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

theorem recurrence2Scalar1Left_coeff_114 :
    recurrence2Scalar1Left.coeff 114 =
      -(((13208303979746668378 * 10 ^ 70 +
        2200042674839423524511229303857503984932560794054223433661961109384872) * 10 ^ 70 +
        9331049231648201940975586957997367717911884794555686904495828503859101) : ℚ) := by
  unfold recurrence2Scalar1Left
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

private theorem recurrence2Scalar1Left_coeff_115_prefix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (115 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (115 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_115 :
    recurrence2Scalar1Left.coeff 115 =
      (((34967296148304676835 * 10 ^ 70 +
        8801768736474968981893191709294076719930098814524901893970445516145991) * 10 ^ 70 +
        7090520676818662430466129567959446227410020870489151017889438048448204) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 116 = 1 +
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
  rw [recurrence2Scalar1Left_coeff_115_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_116_prefix_zero :
    (∑ x ∈ Finset.range 2,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (116 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (116 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_116 :
    recurrence2Scalar1Left.coeff 116 =
      (((169747731020044184023 * 10 ^ 70 +
        3196816149809601874654962733960156653580186635810174211131049595233170) * 10 ^ 70 +
        2439738970147583095772049538756849036178131810223796452971528466757598) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 117 = 2 +
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
  rw [recurrence2Scalar1Left_coeff_116_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_117_prefix_zero :
    (∑ x ∈ Finset.range 3,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (117 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (117 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_117 :
    recurrence2Scalar1Left.coeff 117 =
      -(((1952720754649723920342 * 10 ^ 70 +
        3904033485448048381540033402274760354365452151289145975796009338531075) * 10 ^ 70 +
        8872192464306308884532561057949485229908122578706770990953208288274260) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 118 = 3 +
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
  rw [recurrence2Scalar1Left_coeff_117_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_118_prefix_zero :
    (∑ x ∈ Finset.range 4,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (118 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (118 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_118 :
    recurrence2Scalar1Left.coeff 118 =
      (((9039902728894179916864 * 10 ^ 70 +
        1263050718232424486885229576046665258753497685220233756496268614347719) * 10 ^ 70 +
        2471214133722720782749123327584570862208078892688503725783375176528821) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 119 = 4 +
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
  rw [recurrence2Scalar1Left_coeff_118_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_119_prefix_zero :
    (∑ x ∈ Finset.range 5,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (119 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (119 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_119 :
    recurrence2Scalar1Left.coeff 119 =
      -(((19531281723726574033876 * 10 ^ 70 +
        3615317205525252922993647210532098462646670742550803934836442668175893) * 10 ^ 70 +
        5060781675875647497631006278743434114248550063786357349531425856093179) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 120 = 5 +
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
  rw [recurrence2Scalar1Left_coeff_119_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_120_prefix_zero :
    (∑ x ∈ Finset.range 6,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (120 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (120 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_120 :
    recurrence2Scalar1Left.coeff 120 =
      -(((41343140460340923182745 * 10 ^ 70 +
        1481715032631220400331740291591787098741801898720115086245739622348433) * 10 ^ 70 +
        4519538750303173493840870349340627291619490370715117626670631083800004) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 121 = 6 +
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
  rw [recurrence2Scalar1Left_coeff_120_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_121_prefix_zero :
    (∑ x ∈ Finset.range 7,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (121 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (121 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_121 :
    recurrence2Scalar1Left.coeff 121 =
      (((585223115787761262306295 * 10 ^ 70 +
        7345649998346465818872888866983813482800719291405468654347874926478839) * 10 ^ 70 +
        2549679906297147039613422168348784785771887801163456407447840923318839) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 122 = 7 +
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
  rw [recurrence2Scalar1Left_coeff_121_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_122_prefix_zero :
    (∑ x ∈ Finset.range 8,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (122 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (122 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_122 :
    recurrence2Scalar1Left.coeff 122 =
      -(((2870552622634118107143994 * 10 ^ 70 +
        9474245991050488131671121134302868843852786536220548864686642243847352) * 10 ^ 70 +
        6490812431968605072387475131496481163664081091145903487683462913060471) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 123 = 8 +
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
  rw [recurrence2Scalar1Left_coeff_122_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_123_prefix_zero :
    (∑ x ∈ Finset.range 9,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (123 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (123 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_123 :
    recurrence2Scalar1Left.coeff 123 =
      (((8076916298941546341083877 * 10 ^ 70 +
        5441180495839473007439131428325160327144791381111307056605300398797105) * 10 ^ 70 +
        0762040047163092640989117183826340268415379630069053623812929153366693) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 124 = 9 +
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
  rw [recurrence2Scalar1Left_coeff_123_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_124_prefix_zero :
    (∑ x ∈ Finset.range 10,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (124 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (124 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_124 :
    recurrence2Scalar1Left.coeff 124 =
      -(((4867718824484632258250767 * 10 ^ 70 +
        4704280562182954033924446358077260316721080360856915571835460369858799) * 10 ^ 70 +
        9715672176313101391356137482889547173394243668690761397061650007486605) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 125 = 10 +
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
  rw [recurrence2Scalar1Left_coeff_124_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_125_prefix_zero :
    (∑ x ∈ Finset.range 11,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (125 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (125 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_125 :
    recurrence2Scalar1Left.coeff 125 =
      -(((86288230161021754549433108 * 10 ^ 70 +
        5681000090790968184430344098280616947825482951960889177326433048901490) * 10 ^ 70 +
        4668554592436450750958200368363647133139225435157254202134394787886853) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 126 = 11 +
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
  rw [recurrence2Scalar1Left_coeff_125_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_126_prefix_zero :
    (∑ x ∈ Finset.range 12,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (126 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (126 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_126 :
    recurrence2Scalar1Left.coeff 126 =
      (((545914832944138431445519466 * 10 ^ 70 +
        5238567442471117053599510868833318715500725677845565607038307118239654) * 10 ^ 70 +
        9230107622888619061429610031881314784006099947758941510845574444396485) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 127 = 12 +
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
  rw [recurrence2Scalar1Left_coeff_126_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_127_prefix_zero :
    (∑ x ∈ Finset.range 13,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (127 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (127 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_127 :
    recurrence2Scalar1Left.coeff 127 =
      -(((1869365973441287947418382750 * 10 ^ 70 +
        7229039846632643349627727979045022083703167545474034393069261832644400) * 10 ^ 70 +
        2321626941260221871432870765565521749989853811563617745458315103658833) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 128 = 13 +
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
  rw [recurrence2Scalar1Left_coeff_127_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_128_prefix_zero :
    (∑ x ∈ Finset.range 14,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (128 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (128 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_128 :
    recurrence2Scalar1Left.coeff 128 =
      (((3622327811371649007032362568 * 10 ^ 70 +
        9828432710467789033889134231431524643894571452157730127709654369239634) * 10 ^ 70 +
        6624073148685048620075180796312113487920767612225687047821916344025986) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 129 = 14 +
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
  rw [recurrence2Scalar1Left_coeff_128_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_129_prefix_zero :
    (∑ x ∈ Finset.range 15,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (129 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (129 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_129 :
    recurrence2Scalar1Left.coeff 129 =
      -(((385716782333403218279228019 * 10 ^ 70 +
        7098978510872009906702478602474197815647236298699409398340230252744338) * 10 ^ 70 +
        3609531348388793532436557508756807383334234105580698874530381889801788) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 130 = 15 +
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
  rw [recurrence2Scalar1Left_coeff_129_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_130_prefix_zero :
    (∑ x ∈ Finset.range 16,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (130 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (130 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_130 :
    recurrence2Scalar1Left.coeff 130 =
      -(((27764707804767912443193856061 * 10 ^ 70 +
        1525390368992226495537745958024209597451857540202945323922690568961285) * 10 ^ 70 +
        8930416958082839138182276754249366225313405286196221678805320726410614) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 131 = 16 +
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
  rw [recurrence2Scalar1Left_coeff_130_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_131_prefix_zero :
    (∑ x ∈ Finset.range 17,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (131 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (131 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_131 :
    recurrence2Scalar1Left.coeff 131 =
      (((187725923978735769345393356114 * 10 ^ 70 +
        7871685257667705876556189633683463544802140368150682684470253922164188) * 10 ^ 70 +
        8659674594374807574619328358222918059228298847560504770451741777685525) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 132 = 17 +
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
  rw [recurrence2Scalar1Left_coeff_131_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_132_prefix_zero :
    (∑ x ∈ Finset.range 18,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (132 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (132 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_132 :
    recurrence2Scalar1Left.coeff 132 =
      -(((1255537463073816627690964709496 * 10 ^ 70 +
        0358670084165800723221297300053868349623069561301538077775496585520429) * 10 ^ 70 +
        8981068935262903894733740131398588818660360138902005623521492000690787) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 133 = 18 +
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
  rw [recurrence2Scalar1Left_coeff_132_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_133_prefix_zero :
    (∑ x ∈ Finset.range 19,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (133 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (133 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_133 :
    recurrence2Scalar1Left.coeff 133 =
      (((6878471295454154081282507104375 * 10 ^ 70 +
        3775971198692753578158441407802699239178098990861863990697541523040661) * 10 ^ 70 +
        0507802683272814198294097759135014590943737892666552192513590270365602) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 134 = 19 +
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
  rw [recurrence2Scalar1Left_coeff_133_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_134_prefix_zero :
    (∑ x ∈ Finset.range 20,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (134 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (134 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_134 :
    recurrence2Scalar1Left.coeff 134 =
      -(((22351089418848162812481856621437 * 10 ^ 70 +
        0128014598096167835757137877589973612570548069211231875834996272791187) * 10 ^ 70 +
        6612721906463663578539223700670762843179202443985481555924875491504022) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 135 = 20 +
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
  rw [recurrence2Scalar1Left_coeff_134_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_135_prefix_zero :
    (∑ x ∈ Finset.range 21,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (135 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (135 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_135 :
    recurrence2Scalar1Left.coeff 135 =
      -(((1582714238207805479261439382984 * 10 ^ 70 +
        7836531102875863454479387133392412916045448860707014783228882520537615) * 10 ^ 70 +
        1063776439858500615072829640734977673271314086786814243343343007250947) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 136 = 21 +
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
  rw [recurrence2Scalar1Left_coeff_135_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_136_prefix_zero :
    (∑ x ∈ Finset.range 22,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (136 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (136 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_136 :
    recurrence2Scalar1Left.coeff 136 =
      (((440112010991455288111330912136610 * 10 ^ 70 +
        2245507660140772756280040498200988543778714113532553468867678508967791) * 10 ^ 70 +
        5389735840693694004755938340618642643559331832527702835228900451090677) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 137 = 22 +
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
  rw [recurrence2Scalar1Left_coeff_136_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_137_prefix_zero :
    (∑ x ∈ Finset.range 23,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (137 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (137 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_137 :
    recurrence2Scalar1Left.coeff 137 =
      -(((2334500998518826489246603433969813 * 10 ^ 70 +
        6783458769458693586900915695621087079847689843554377293319201311830335) * 10 ^ 70 +
        2391094028710648432839165917714463446209898444123756245071560072767502) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 138 = 23 +
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
  rw [recurrence2Scalar1Left_coeff_137_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_138_prefix_zero :
    (∑ x ∈ Finset.range 24,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (138 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (138 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_138 :
    recurrence2Scalar1Left.coeff 138 =
      (((4649031313326225205289398230376719 * 10 ^ 70 +
        2468772059077008742955539647208901488729883912146755696135275558675648) * 10 ^ 70 +
        0238754474345751469011054849011349059794458498702204358071468983718477) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 139 = 24 +
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
  rw [recurrence2Scalar1Left_coeff_138_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_139_prefix_zero :
    (∑ x ∈ Finset.range 25,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (139 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (139 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_139 :
    recurrence2Scalar1Left.coeff 139 =
      (((11951121004976412944500149983293480 * 10 ^ 70 +
        0973192255074896872128794814515736755258294938922164990335995088636905) * 10 ^ 70 +
        7255985075742362165532453808569301961656468656263141008402856449676766) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 140 = 25 +
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
  rw [recurrence2Scalar1Left_coeff_139_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_140_prefix_zero :
    (∑ x ∈ Finset.range 26,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (140 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (140 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_140 :
    recurrence2Scalar1Left.coeff 140 =
      -(((108870007957691461494930233051977530 * 10 ^ 70 +
        3974471080343940417576259456715936380040508119904184023744042090920654) * 10 ^ 70 +
        7764084818683876794750644131713856655638221519260837651871354869735196) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 141 = 26 +
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
  rw [recurrence2Scalar1Left_coeff_140_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_141_prefix_zero :
    (∑ x ∈ Finset.range 27,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (141 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (141 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_141 :
    recurrence2Scalar1Left.coeff 141 =
      (((253986497144733626297762883514245464 * 10 ^ 70 +
        6561827160314965343620233559241339196607667820401462098699640319790864) * 10 ^ 70 +
        6930375448346038976083305297894769252430027921432827963691519120489478) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 142 = 27 +
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
  rw [recurrence2Scalar1Left_coeff_141_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_142_prefix_zero :
    (∑ x ∈ Finset.range 28,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (142 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (142 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_142 :
    recurrence2Scalar1Left.coeff 142 =
      (((476235707580260228613125738759038888 * 10 ^ 70 +
        3683118135256697637720149595508385532675141961664096021093830086021933) * 10 ^ 70 +
        8716176116344130875756669286960014687665687443100855769576600879975467) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 143 = 28 +
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
  rw [recurrence2Scalar1Left_coeff_142_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_143_prefix_zero :
    (∑ x ∈ Finset.range 29,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (143 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (143 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_143 :
    recurrence2Scalar1Left.coeff 143 =
      -(((4804596440483754350614904255409220753 * 10 ^ 70 +
        6972450919738188923245168213985088460821208849754637367166394553595025) * 10 ^ 70 +
        1886612232307267270160184235696705045088436978718956467886092035458285) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 144 = 29 +
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
  rw [recurrence2Scalar1Left_coeff_143_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_144_prefix_zero :
    (∑ x ∈ Finset.range 30,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (144 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (144 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_144 :
    recurrence2Scalar1Left.coeff 144 =
      (((9613246269561793135712299789447652302 * 10 ^ 70 +
        2559246390276963665610839420485833646661472077528803978457409765636282) * 10 ^ 70 +
        7297569571949006795413292514278055497605011043179337088114186911346471) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 145 = 30 +
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
  rw [recurrence2Scalar1Left_coeff_144_prefix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
