/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupLeadingSquare
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupA2
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar2LeftPart0Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: Scalar2Left coefficient convolution

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
  recurrence2A2_coeff_0
  recurrence2A2_coeff_1
  recurrence2A2_coeff_2
  recurrence2A2_coeff_3
  recurrence2A2_coeff_4
  recurrence2A2_coeff_5
  recurrence2A2_coeff_6
  recurrence2A2_coeff_7
  recurrence2A2_coeff_8
  recurrence2A2_coeff_9
  recurrence2A2_coeff_10
  recurrence2A2_coeff_11
  recurrence2A2_coeff_12
  recurrence2A2_coeff_13
  recurrence2A2_coeff_14
  recurrence2A2_coeff_15
  recurrence2A2_coeff_16
  recurrence2A2_coeff_17
  recurrence2A2_coeff_18
  recurrence2A2_coeff_19
  recurrence2A2_coeff_20
  recurrence2A2_coeff_21
  recurrence2A2_coeff_22
  recurrence2A2_coeff_23
  recurrence2A2_coeff_24
  recurrence2A2_coeff_25
  recurrence2A2_coeff_26
  recurrence2A2_coeff_27
  recurrence2A2_coeff_28
  recurrence2A2_coeff_29
  recurrence2A2_coeff_30
  recurrence2A2_coeff_31
  recurrence2A2_coeff_32
  recurrence2A2_coeff_33
  recurrence2A2_coeff_34
  recurrence2A2_coeff_35
  recurrence2A2_coeff_36
  recurrence2A2_coeff_37
  recurrence2A2_coeff_38
  recurrence2A2_coeff_39
  recurrence2A2_coeff_40
  recurrence2A2_coeff_41
  recurrence2A2_coeff_42
  recurrence2A2_coeff_43
  recurrence2A2_coeff_44
  recurrence2A2_coeff_45
  recurrence2A2_coeff_46
  recurrence2A2_coeff_47
  recurrence2A2_coeff_48
  recurrence2A2_coeff_49
  recurrence2A2_coeff_50
  recurrence2A2_coeff_51
  recurrence2A2_coeff_52
  recurrence2A2_coeff_53
  recurrence2A2_coeff_54
  recurrence2A2_coeff_55
  recurrence2A2_coeff_56
  recurrence2A2_coeff_57
  recurrence2A2_coeff_58
  recurrence2A2_coeff_59
  recurrence2A2_coeff_60
  recurrence2A2_coeff_61
  recurrence2A2_coeff_62
  recurrence2A2_coeff_63
  recurrence2A2_coeff_64
  recurrence2A2_coeff_65
  recurrence2A2_coeff_66
  recurrence2A2_coeff_67
  recurrence2A2_coeff_68
  recurrence2A2_coeff_69
  recurrence2A2_coeff_70
  recurrence2A2_coeff_71
  recurrence2A2_coeff_72
  recurrence2A2_coeff_73
  recurrence2A2_coeff_74
  recurrence2A2_coeff_75
  recurrence2A2_coeff_76
  recurrence2A2_coeff_77
  recurrence2A2_coeff_78
  recurrence2A2_coeff_79
  recurrence2A2_coeff_80
  recurrence2A2_coeff_81
  recurrence2A2_coeff_82
  recurrence2A2_coeff_83
  recurrence2A2_coeff_84
  recurrence2A2_coeff_85
  recurrence2A2_coeff_86
  recurrence2A2_coeff_87
  recurrence2A2_coeff_88
  recurrence2A2_coeff_89
  recurrence2A2_coeff_90
  recurrence2A2_coeff_91
  recurrence2A2_coeff_92
  recurrence2A2_coeff_93
  recurrence2A2_coeff_94
  recurrence2A2_coeff_95
  recurrence2A2_coeff_96
  recurrence2A2_coeff_97
  recurrence2A2_coeff_98
  recurrence2A2_coeff_99
  recurrence2A2_coeff_100
  recurrence2A2_coeff_101
  recurrence2A2_coeff_102
  recurrence2A2_coeff_103
  recurrence2A2_coeff_104
  recurrence2A2_coeff_105
  recurrence2A2_coeff_106
  recurrence2A2_coeff_107
  recurrence2A2_coeff_108
  recurrence2A2_coeff_109
  recurrence2A2_coeff_110

theorem recurrence2Scalar2Left_coeff_93 :
    recurrence2Scalar2Left.coeff 93 =
      (((110750537 * 10 ^ 70 +
        4995669635804239534296981406371286107366875798566907658045346855113144) * 10 ^ 70 +
        9961038416884765583141452005691749693937861754762286756775966311017216) : ℚ) := by
  unfold recurrence2Scalar2Left
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

theorem recurrence2Scalar2Left_coeff_94 :
    recurrence2Scalar2Left.coeff 94 =
      -(((480618954 * 10 ^ 70 +
        4187930798802087809635982444135270656968560902869196564171259162137220) * 10 ^ 70 +
        6174566730615133035107483511756973278118252330677627398312176458221574) : ℚ) := by
  unfold recurrence2Scalar2Left
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

theorem recurrence2Scalar2Left_coeff_95 :
    recurrence2Scalar2Left.coeff 95 =
      (((1995867994 * 10 ^ 70 +
        0840208892115475319013622326370805407553491351947249768036286983324307) * 10 ^ 70 +
        7689112499589817929270241077084499237235259541027655908562686125084557) : ℚ) := by
  unfold recurrence2Scalar2Left
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

theorem recurrence2Scalar2Left_coeff_96 :
    recurrence2Scalar2Left.coeff 96 =
      -(((7908057620 * 10 ^ 70 +
        5540486363738516240764921395181744783010647754621221727860199039553092) * 10 ^ 70 +
        0869870350454211197482112877424361627301460337982884906691874443523109) : ℚ) := by
  unfold recurrence2Scalar2Left
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

theorem recurrence2Scalar2Left_coeff_97 :
    recurrence2Scalar2Left.coeff 97 =
      (((29753391637 * 10 ^ 70 +
        9208967099318128650818189559640235414801776678576127776354989385551877) * 10 ^ 70 +
        6195738902538895848883022449654068233916569077860059210327873913635797) : ℚ) := by
  unfold recurrence2Scalar2Left
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

theorem recurrence2Scalar2Left_coeff_98 :
    recurrence2Scalar2Left.coeff 98 =
      -(((105486408693 * 10 ^ 70 +
        2920197326985262472210806823126484681852550358619061222431689618576429) * 10 ^ 70 +
        3943136503327418033177315439347098628016557348539220542693472902592476) : ℚ) := by
  unfold recurrence2Scalar2Left
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

theorem recurrence2Scalar2Left_coeff_99 :
    recurrence2Scalar2Left.coeff 99 =
      (((348109772068 * 10 ^ 70 +
        0646987760169022218681587676120995559056535529934714767638287019410791) * 10 ^ 70 +
        2669835253533309567857371731028383703159144750910044415363662242083572) : ℚ) := by
  unfold recurrence2Scalar2Left
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

theorem recurrence2Scalar2Left_coeff_100 :
    recurrence2Scalar2Left.coeff 100 =
      -(((1047388959452 * 10 ^ 70 +
        3055630043844087336680505867862132319865875767805601909475097568192790) * 10 ^ 70 +
        3431851935758510073060857296576852761961172693490102403278436093222549) : ℚ) := by
  unfold recurrence2Scalar2Left
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

theorem recurrence2Scalar2Left_coeff_101 :
    recurrence2Scalar2Left.coeff 101 =
      (((2759123793250 * 10 ^ 70 +
        4436006089038523505925148985959553812096876590694670963202441663407749) * 10 ^ 70 +
        0628203879068108087827573582239337744839225002103720888719262101308628) : ℚ) := by
  unfold recurrence2Scalar2Left
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

theorem recurrence2Scalar2Left_coeff_102 :
    recurrence2Scalar2Left.coeff 102 =
      -(((5711470699689 * 10 ^ 70 +
        5158524814152394345425984306369581810406162587924040042301374351188106) * 10 ^ 70 +
        0394851372440432662140215652624315386459180399768460869826228336819673) : ℚ) := by
  unfold recurrence2Scalar2Left
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

theorem recurrence2Scalar2Left_coeff_103 :
    recurrence2Scalar2Left.coeff 103 =
      (((4939439120261 * 10 ^ 70 +
        9214326135780747739736328897531505014302339485480813741884711227284589) * 10 ^ 70 +
        4183911130841754581632373643363411306133412278359290830920179140895469) : ℚ) := by
  unfold recurrence2Scalar2Left
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

theorem recurrence2Scalar2Left_coeff_104 :
    recurrence2Scalar2Left.coeff 104 =
      (((35049060282897 * 10 ^ 70 +
        2901016378588714825129821331176752722315325777710256676487647625038608) * 10 ^ 70 +
        7308906080731874383029978262060384437649980135216089853261286922892291) : ℚ) := by
  unfold recurrence2Scalar2Left
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

theorem recurrence2Scalar2Left_coeff_105 :
    recurrence2Scalar2Left.coeff 105 =
      -(((294628083892778 * 10 ^ 70 +
        6006164529103424179656909038303619906236925636469584085515981038333577) * 10 ^ 70 +
        2580695116794888719482095224986045507210826777996240641303292567170666) : ℚ) := by
  unfold recurrence2Scalar2Left
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

theorem recurrence2Scalar2Left_coeff_106 :
    recurrence2Scalar2Left.coeff 106 =
      (((1577523997002417 * 10 ^ 70 +
        9117567535738913962118180721964072162974932058298931315316106994591869) * 10 ^ 70 +
        3355470332640236053138468571821038117955276715918668349389258879251319) : ℚ) := by
  unfold recurrence2Scalar2Left
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

theorem recurrence2Scalar2Left_coeff_107 :
    recurrence2Scalar2Left.coeff 107 =
      -(((7146726586652096 * 10 ^ 70 +
        5678653428112982920323280855893833776989619865215998929346623405182403) * 10 ^ 70 +
        9631302511395179571262401985709145371607260371671471282905814246198465) : ℚ) := by
  unfold recurrence2Scalar2Left
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

theorem recurrence2Scalar2Left_coeff_108 :
    recurrence2Scalar2Left.coeff 108 =
      (((28783499981503978 * 10 ^ 70 +
        6061486868497233682523057676129888152826969463640896078788572449709904) * 10 ^ 70 +
        0738872766876882472301154626611621610389298905559873378853614077290511) : ℚ) := by
  unfold recurrence2Scalar2Left
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

theorem recurrence2Scalar2Left_coeff_109 :
    recurrence2Scalar2Left.coeff 109 =
      -(((101539121113156348 * 10 ^ 70 +
        7551868558879037525371044358408408385431791899266583882654767909788972) * 10 ^ 70 +
        7371097839370509223539173719557982337513715143044423376681893031554326) : ℚ) := by
  unfold recurrence2Scalar2Left
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

theorem recurrence2Scalar2Left_coeff_110 :
    recurrence2Scalar2Left.coeff 110 =
      (((295147199332691408 * 10 ^ 70 +
        6575454669281788409747840779553667543902256425917434202233117153526619) * 10 ^ 70 +
        9980086912351720366981592961184720245342316469841236934139682445478348) : ℚ) := by
  unfold recurrence2Scalar2Left
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

private theorem recurrence2Scalar2Left_coeff_111_prefix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (111 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (111 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_111 :
    recurrence2Scalar2Left.coeff 111 =
      -(((603037210445030539 * 10 ^ 70 +
        8227675897735096385406038407284231872541427648185817486553350361090549) * 10 ^ 70 +
        1570479626503393551660407044313768720304062641578076550695770513256975) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 112 = 1 +
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
  rw [recurrence2Scalar2Left_coeff_111_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_112_prefix_zero :
    (∑ x ∈ Finset.range 2,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (112 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (112 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_112 :
    recurrence2Scalar2Left.coeff 112 =
      (((327214845053100867 * 10 ^ 70 +
        1580667912212795392157941570719431702306275607904707287058759273899971) * 10 ^ 70 +
        0609270008216939799828996486583890000795941047273016516240421730449547) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 113 = 2 +
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
  rw [recurrence2Scalar2Left_coeff_112_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_113_prefix_zero :
    (∑ x ∈ Finset.range 3,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (113 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (113 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_113 :
    recurrence2Scalar2Left.coeff 113 =
      (((2791505203595608298 * 10 ^ 70 +
        5528195553966971435825822525347589861253251093973111743621044911786202) * 10 ^ 70 +
        6788592377349290524621659500044288112934555299615143212147988331285603) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 114 = 3 +
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
  rw [recurrence2Scalar2Left_coeff_113_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_114_prefix_zero :
    (∑ x ∈ Finset.range 4,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (114 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (114 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_114 :
    recurrence2Scalar2Left.coeff 114 =
      -(((4660965901662127327 * 10 ^ 70 +
        8777928592814333301248571977023417480918390189081219233959475632516827) * 10 ^ 70 +
        8898011189322819150696292997825436835463339639547806066270346644658103) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 115 = 4 +
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
  rw [recurrence2Scalar2Left_coeff_114_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_115_prefix_zero :
    (∑ x ∈ Finset.range 5,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (115 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (115 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_115 :
    recurrence2Scalar2Left.coeff 115 =
      -(((69356656309833083646 * 10 ^ 70 +
        0826803773469910416112990821254987699794437632654296944374562513857922) * 10 ^ 70 +
        6390696744432411506557306054353767820589073038035436283524808636260083) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 116 = 5 +
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
  rw [recurrence2Scalar2Left_coeff_115_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_116_prefix_zero :
    (∑ x ∈ Finset.range 6,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (116 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (116 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_116 :
    recurrence2Scalar2Left.coeff 116 =
      (((591132049616009560185 * 10 ^ 70 +
        6590226633526149816552916329684546839585370209540193680058702546052107) * 10 ^ 70 +
        3784603046274956313558621377840132212035268893423044296023231626034381) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 117 = 6 +
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
  rw [recurrence2Scalar2Left_coeff_116_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_117_prefix_zero :
    (∑ x ∈ Finset.range 7,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (117 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (117 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_117 :
    recurrence2Scalar2Left.coeff 117 =
      -(((2385268315679782208304 * 10 ^ 70 +
        9619326207313067030350194096600439232876111796361525938364391242972826) * 10 ^ 70 +
        5653362794518184824257584791692427398496528370806349974059788756661638) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 118 = 7 +
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
  rw [recurrence2Scalar2Left_coeff_117_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_118_prefix_zero :
    (∑ x ∈ Finset.range 8,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (118 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (118 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_118 :
    recurrence2Scalar2Left.coeff 118 =
      (((3675673711831537910988 * 10 ^ 70 +
        3791040414879583335198097374498096964061972867794117835691204812487774) * 10 ^ 70 +
        3434106324657396082072659228927284180030034670691417330198418681004654) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 119 = 8 +
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
  rw [recurrence2Scalar2Left_coeff_118_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_119_prefix_zero :
    (∑ x ∈ Finset.range 9,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (119 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (119 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_119 :
    recurrence2Scalar2Left.coeff 119 =
      (((20387067810673547168849 * 10 ^ 70 +
        2220420644227886232639114249008983642245671186290737387161215869415913) * 10 ^ 70 +
        7861293374270301008539667309477790390209869211934343126684498483924420) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 120 = 9 +
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
  rw [recurrence2Scalar2Left_coeff_119_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_120_prefix_zero :
    (∑ x ∈ Finset.range 10,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (120 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (120 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_120 :
    recurrence2Scalar2Left.coeff 120 =
      -(((188948693330150072889785 * 10 ^ 70 +
        1392628616119334836411130944592224070753835678261221294291490240892257) * 10 ^ 70 +
        4704850616212331059073504804557281272072908562380980248039415156396368) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 121 = 10 +
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
  rw [recurrence2Scalar2Left_coeff_120_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_121_prefix_zero :
    (∑ x ∈ Finset.range 11,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (121 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (121 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_121 :
    recurrence2Scalar2Left.coeff 121 =
      (((819959092267795427192817 * 10 ^ 70 +
        9235292478001085304336694895261968060681278354681758661526348029911634) * 10 ^ 70 +
        2023394560513237542538648576152916041439527149873261022352306795300590) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 122 = 11 +
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
  rw [recurrence2Scalar2Left_coeff_121_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_122_prefix_zero :
    (∑ x ∈ Finset.range 12,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (122 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (122 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_122 :
    recurrence2Scalar2Left.coeff 122 =
      -(((2000008450998648168560548 * 10 ^ 70 +
        6581300383602922494153546917506757369613900102431661475936919386709525) * 10 ^ 70 +
        9195455862955669011682070767945545032174573412049912564592067282257073) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 123 = 12 +
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
  rw [recurrence2Scalar2Left_coeff_122_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_123_prefix_zero :
    (∑ x ∈ Finset.range 13,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (123 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (123 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_123 :
    recurrence2Scalar2Left.coeff 123 =
      -(((286508625990672102212959 * 10 ^ 70 +
        8793813994707414679390281830315290321806533839920546957429868227156841) * 10 ^ 70 +
        0344284976658183777352780190472584319004302064102064610814931895404806) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 124 = 13 +
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
  rw [recurrence2Scalar2Left_coeff_123_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_124_prefix_zero :
    (∑ x ∈ Finset.range 14,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (124 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (124 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_124 :
    recurrence2Scalar2Left.coeff 124 =
      (((29477000068265375264372521 * 10 ^ 70 +
        0937182434223207626460541791191179667919572250625278307341911154336151) * 10 ^ 70 +
        7250286497600628544817710693240273732534047600838729981873295385151395) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 125 = 14 +
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
  rw [recurrence2Scalar2Left_coeff_124_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_125_prefix_zero :
    (∑ x ∈ Finset.range 15,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (125 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (125 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_125 :
    recurrence2Scalar2Left.coeff 125 =
      -(((159436638158268716271420359 * 10 ^ 70 +
        5656698873865363659162885164590177463811342622338465201158674421820510) * 10 ^ 70 +
        2497885193493708807802537077890337017641258571705239226462225192590515) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 126 = 15 +
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
  rw [recurrence2Scalar2Left_coeff_125_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_126_prefix_zero :
    (∑ x ∈ Finset.range 16,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (126 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (126 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_126 :
    recurrence2Scalar2Left.coeff 126 =
      (((493727847568537859441292417 * 10 ^ 70 +
        7958873600993537205471979384721145814201773190332412507254403595179098) * 10 ^ 70 +
        0328195972880713348463279165809311186666230691125682409316924532132509) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 127 = 16 +
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
  rw [recurrence2Scalar2Left_coeff_126_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_127_prefix_zero :
    (∑ x ∈ Finset.range 17,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (127 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (127 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_127 :
    recurrence2Scalar2Left.coeff 127 =
      -(((804274598873378963028854377 * 10 ^ 70 +
        0909997052603731307768899730880621486042812572690308178093381035434539) * 10 ^ 70 +
        2838337364406448984081501525083507732603263662328557055134241370810749) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 128 = 17 +
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
  rw [recurrence2Scalar2Left_coeff_127_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_128_prefix_zero :
    (∑ x ∈ Finset.range 18,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (128 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (128 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_128 :
    recurrence2Scalar2Left.coeff 128 =
      -(((610417412017172978239604666 * 10 ^ 70 +
        6134059342812843007596453179919163718362284638473768392928946242953415) * 10 ^ 70 +
        5002779087565077849172843115592670902549381672359327471048817362041434) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 129 = 18 +
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
  rw [recurrence2Scalar2Left_coeff_128_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_129_prefix_zero :
    (∑ x ∈ Finset.range 19,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (129 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (129 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_129 :
    recurrence2Scalar2Left.coeff 129 =
      (((9970112345969774779205332378 * 10 ^ 70 +
        0427880742014842656109938676771765916157948240316682894036222050094118) * 10 ^ 70 +
        9242332488349824889947062339511606444365282033203281972743293407336589) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 130 = 19 +
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
  rw [recurrence2Scalar2Left_coeff_129_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_130_prefix_zero :
    (∑ x ∈ Finset.range 20,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (130 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (130 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_130 :
    recurrence2Scalar2Left.coeff 130 =
      -(((62167275467623010426248473771 * 10 ^ 70 +
        1202274939820260169652011961515732767701993362514596554388925258731775) * 10 ^ 70 +
        6096353495467994665822142847580782463560293006422070907282566680856615) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 131 = 20 +
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
  rw [recurrence2Scalar2Left_coeff_130_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_131_prefix_zero :
    (∑ x ∈ Finset.range 21,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (131 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (131 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_131 :
    recurrence2Scalar2Left.coeff 131 =
      (((390202708230716084851433544787 * 10 ^ 70 +
        8012708605404110295415912745530882881709475787491474040176882981134684) * 10 ^ 70 +
        4684516646374927399022830306504620954028037055958046274269966192522011) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 132 = 21 +
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
  rw [recurrence2Scalar2Left_coeff_131_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_132_prefix_zero :
    (∑ x ∈ Finset.range 22,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (132 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (132 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_132 :
    recurrence2Scalar2Left.coeff 132 =
      -(((1948607952975093306933102461500 * 10 ^ 70 +
        2937864640010854569433067082555523561831556975536007331949089967146097) * 10 ^ 70 +
        1584457896185144552164998392145693277881411611521433559135005813749721) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 133 = 22 +
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
  rw [recurrence2Scalar2Left_coeff_132_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_133_prefix_zero :
    (∑ x ∈ Finset.range 23,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (133 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (133 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_133 :
    recurrence2Scalar2Left.coeff 133 =
      (((5338129563563850753221627419211 * 10 ^ 70 +
        9705819205502101935653100792594129925882340132698988506543157209798291) * 10 ^ 70 +
        2083032858523910509815395626188073444106837653671710104420975584455814) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 134 = 23 +
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
  rw [recurrence2Scalar2Left_coeff_133_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_134_prefix_zero :
    (∑ x ∈ Finset.range 24,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (134 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (134 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_134 :
    recurrence2Scalar2Left.coeff 134 =
      (((6915140193779832442769052647651 * 10 ^ 70 +
        0028311585555640404353729164193514892793430160866001612064321551945990) * 10 ^ 70 +
        0913026241269676191034529579976316393581756031436065450096431847535802) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 135 = 24 +
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
  rw [recurrence2Scalar2Left_coeff_134_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_135_prefix_zero :
    (∑ x ∈ Finset.range 25,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (135 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (135 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_135 :
    recurrence2Scalar2Left.coeff 135 =
      -(((142406237510490359732166699053264 * 10 ^ 70 +
        3384186904319565676234206083806277749193503682252932792821996529565260) * 10 ^ 70 +
        5589932306325415316067291954743848663247857971235773587186820938829983) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 136 = 25 +
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
  rw [recurrence2Scalar2Left_coeff_135_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_136_prefix_zero :
    (∑ x ∈ Finset.range 26,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (136 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (136 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_136 :
    recurrence2Scalar2Left.coeff 136 =
      (((641575748012554940701639866672881 * 10 ^ 70 +
        5790810425655249490388209686558088162461313506021313593787508135914965) * 10 ^ 70 +
        7590401964461333625102557322189403394520187499622515570929911952328377) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 137 = 26 +
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
  rw [recurrence2Scalar2Left_coeff_136_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_137_prefix_zero :
    (∑ x ∈ Finset.range 27,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (137 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (137 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_137 :
    recurrence2Scalar2Left.coeff 137 =
      -(((943121543616786591393813185590696 * 10 ^ 70 +
        2201342167019073145014932844853658428846234407280807746675939210815219) * 10 ^ 70 +
        0075683049687187329430670233365665819226702251572103151537500912098620) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 138 = 27 +
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
  rw [recurrence2Scalar2Left_coeff_137_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_138_prefix_zero :
    (∑ x ∈ Finset.range 28,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (138 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (138 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_138 :
    recurrence2Scalar2Left.coeff 138 =
      -(((4755637732811673907958559254412108 * 10 ^ 70 +
        9697892379630623126233099901548506000017071830528037777169079188120417) * 10 ^ 70 +
        9036164980065071099619181968516041924510413315132771504871821626763213) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 139 = 28 +
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
  rw [recurrence2Scalar2Left_coeff_138_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_139_prefix_zero :
    (∑ x ∈ Finset.range 29,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (139 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (139 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_139 :
    recurrence2Scalar2Left.coeff 139 =
      (((31373410101635322863183060631842496 * 10 ^ 70 +
        8120012600902031883455110294726681325154926449630785075410883095521754) * 10 ^ 70 +
        1017870071978803278832513834338848301556075767353236041906971327667493) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 140 = 29 +
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
  rw [recurrence2Scalar2Left_coeff_139_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_140_prefix_zero :
    (∑ x ∈ Finset.range 30,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (140 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (140 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_140 :
    recurrence2Scalar2Left.coeff 140 =
      -(((56117131295889923502930875219832196 * 10 ^ 70 +
        6381979460124733977416949170232516870197983816163565399525607666054774) * 10 ^ 70 +
        0238440523107569280260552476502169614678774819515091626738967775126452) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 141 = 30 +
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
  rw [recurrence2Scalar2Left_coeff_140_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_141_prefix_zero :
    (∑ x ∈ Finset.range 31,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (141 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (141 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_141 :
    recurrence2Scalar2Left.coeff 141 =
      -(((198555272826095366479696891782858040 * 10 ^ 70 +
        0068489366005921229416792238521561484643754569744706359748244894485004) * 10 ^ 70 +
        8296443245048227937575866219921471982817683847045285603679664852006390) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 142 = 31 +
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
  rw [recurrence2Scalar2Left_coeff_141_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_142_prefix_zero :
    (∑ x ∈ Finset.range 32,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (142 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (142 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_142 :
    recurrence2Scalar2Left.coeff 142 =
      (((1377377562692175692561221473915166192 * 10 ^ 70 +
        8632652763232251234326377030118023676917135364430026864167351942242425) * 10 ^ 70 +
        4115661039536121228532264650646430320159761030850824244895647511752674) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 143 = 32 +
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
  rw [recurrence2Scalar2Left_coeff_142_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_143_prefix_zero :
    (∑ x ∈ Finset.range 33,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (143 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (143 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_143 :
    recurrence2Scalar2Left.coeff 143 =
      -(((1955264128165858640711612130657937225 * 10 ^ 70 +
        5520466555153254858174517115275788996897671860354858506105593400661382) * 10 ^ 70 +
        2351529906746694783423131813659959665684036431689525391355945379163171) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 144 = 33 +
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
  rw [recurrence2Scalar2Left_coeff_143_prefix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
