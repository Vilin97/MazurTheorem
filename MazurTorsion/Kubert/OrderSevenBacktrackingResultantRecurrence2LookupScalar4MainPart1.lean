/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB4
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupQuotientConstant
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: Scalar4Main coefficient convolution

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence2B4_coeff_0
  recurrence2B4_coeff_1
  recurrence2B4_coeff_2
  recurrence2B4_coeff_3
  recurrence2B4_coeff_4
  recurrence2B4_coeff_5
  recurrence2B4_coeff_6
  recurrence2B4_coeff_7
  recurrence2B4_coeff_8
  recurrence2B4_coeff_9
  recurrence2B4_coeff_10
  recurrence2B4_coeff_11
  recurrence2B4_coeff_12
  recurrence2B4_coeff_13
  recurrence2B4_coeff_14
  recurrence2B4_coeff_15
  recurrence2B4_coeff_16
  recurrence2B4_coeff_17
  recurrence2B4_coeff_18
  recurrence2B4_coeff_19
  recurrence2B4_coeff_20
  recurrence2B4_coeff_21
  recurrence2B4_coeff_22
  recurrence2B4_coeff_23
  recurrence2B4_coeff_24
  recurrence2B4_coeff_25
  recurrence2B4_coeff_26
  recurrence2B4_coeff_27
  recurrence2B4_coeff_28
  recurrence2B4_coeff_29
  recurrence2B4_coeff_30
  recurrence2B4_coeff_31
  recurrence2B4_coeff_32
  recurrence2B4_coeff_33
  recurrence2B4_coeff_34
  recurrence2B4_coeff_35
  recurrence2B4_coeff_36
  recurrence2B4_coeff_37
  recurrence2B4_coeff_38
  recurrence2B4_coeff_39
  recurrence2B4_coeff_40
  recurrence2B4_coeff_41
  recurrence2B4_coeff_42
  recurrence2B4_coeff_43
  recurrence2B4_coeff_44
  recurrence2B4_coeff_45
  recurrence2B4_coeff_46
  recurrence2B4_coeff_47
  recurrence2B4_coeff_48
  recurrence2B4_coeff_49
  recurrence2B4_coeff_50
  recurrence2B4_coeff_51
  recurrence2B4_coeff_52
  recurrence2B4_coeff_53
  recurrence2B4_coeff_54
  recurrence2B4_coeff_55
  recurrence2B4_coeff_56
  recurrence2B4_coeff_57
  recurrence2B4_coeff_58
  recurrence2B4_coeff_59
  recurrence2B4_coeff_60
  recurrence2B4_coeff_61
  recurrence2B4_coeff_62
  recurrence2B4_coeff_63
  recurrence2B4_coeff_64
  recurrence2B4_coeff_65
  recurrence2B4_coeff_66
  recurrence2B4_coeff_67
  recurrence2B4_coeff_68
  recurrence2B4_coeff_69
  recurrence2B4_coeff_70
  recurrence2B4_coeff_71
  recurrence2B4_coeff_72
  recurrence2B4_coeff_73
  recurrence2B4_coeff_74
  recurrence2B4_coeff_75
  recurrence2B4_coeff_76
  recurrence2B4_coeff_77
  recurrence2B4_coeff_78
  recurrence2B4_coeff_79
  recurrence2B4_coeff_80
  recurrence2B4_coeff_81
  recurrence2B4_coeff_82
  recurrence2B4_coeff_83
  recurrence2B4_coeff_84
  recurrence2B4_coeff_85
  recurrence2B4_coeff_86
  recurrence2B4_coeff_87
  recurrence2B4_coeff_88
  recurrence2B4_coeff_89
  recurrence2B4_coeff_90
  recurrence2B4_coeff_91
  recurrence2B4_coeff_92
  recurrence2B4_coeff_93
  recurrence2B4_coeff_94
  recurrence2B4_coeff_95
  recurrence2B4_coeff_96
  recurrence2B4_coeff_97
  recurrence2B4_coeff_98
  recurrence2B4_coeff_99
  recurrence2B4_coeff_100
  recurrence2B4_coeff_101
  recurrence2B4_coeff_102
  recurrence2B4_coeff_103
  recurrence2B4_coeff_104
  recurrence2B4_coeff_105
  recurrence2B4_coeff_106
  recurrence2B4_coeff_107
  recurrence2B4_coeff_108
  recurrence2B4_coeff_109
  recurrence2B4_coeff_110
  recurrence2B4_coeff_111
  recurrence2B4_coeff_112
  recurrence2B4_coeff_113
  recurrence2B4_coeff_114
  recurrence2B4_coeff_115
  recurrence2B4_coeff_116
  recurrence2B4_coeff_117
  recurrence2B4_coeff_118
  recurrence2B4_coeff_119
  recurrence2B4_coeff_120
  recurrence2B4_coeff_121
  recurrence2B4_coeff_122
  recurrence2B4_coeff_123
  recurrence2B4_coeff_124
  recurrence2B4_coeff_125
  recurrence2B4_coeff_126
  recurrence2B4_coeff_127
  recurrence2B4_coeff_128
  recurrence2B4_coeff_129
  recurrence2B4_coeff_130
  recurrence2B4_coeff_131
  recurrence2B4_coeff_132
  recurrence2B4_coeff_133
  recurrence2B4_coeff_134
  recurrence2B4_coeff_135
  recurrence2B4_coeff_136
  recurrence2B4_coeff_137
  recurrence2B4_coeff_138
  recurrence2QuotientConstant_coeff_0
  recurrence2QuotientConstant_coeff_1
  recurrence2QuotientConstant_coeff_2
  recurrence2QuotientConstant_coeff_3
  recurrence2QuotientConstant_coeff_4
  recurrence2QuotientConstant_coeff_5
  recurrence2QuotientConstant_coeff_6
  recurrence2QuotientConstant_coeff_7
  recurrence2QuotientConstant_coeff_8
  recurrence2QuotientConstant_coeff_9
  recurrence2QuotientConstant_coeff_10
  recurrence2QuotientConstant_coeff_11
  recurrence2QuotientConstant_coeff_12
  recurrence2QuotientConstant_coeff_13
  recurrence2QuotientConstant_coeff_14
  recurrence2QuotientConstant_coeff_15
  recurrence2QuotientConstant_coeff_16
  recurrence2QuotientConstant_coeff_17
  recurrence2QuotientConstant_coeff_18
  recurrence2QuotientConstant_coeff_19
  recurrence2QuotientConstant_coeff_20
  recurrence2QuotientConstant_coeff_21
  recurrence2QuotientConstant_coeff_22
  recurrence2QuotientConstant_coeff_23
  recurrence2QuotientConstant_coeff_24
  recurrence2QuotientConstant_coeff_25
  recurrence2QuotientConstant_coeff_26
  recurrence2QuotientConstant_coeff_27
  recurrence2QuotientConstant_coeff_28
  recurrence2QuotientConstant_coeff_29
  recurrence2QuotientConstant_coeff_30
  recurrence2QuotientConstant_coeff_31
  recurrence2QuotientConstant_coeff_32
  recurrence2QuotientConstant_coeff_33
  recurrence2QuotientConstant_coeff_34
  recurrence2QuotientConstant_coeff_35
  recurrence2QuotientConstant_coeff_36
  recurrence2QuotientConstant_coeff_37
  recurrence2QuotientConstant_coeff_38
  recurrence2QuotientConstant_coeff_39
  recurrence2QuotientConstant_coeff_40
  recurrence2QuotientConstant_coeff_41
  recurrence2QuotientConstant_coeff_42
  recurrence2QuotientConstant_coeff_43
  recurrence2QuotientConstant_coeff_44
  recurrence2QuotientConstant_coeff_45
  recurrence2QuotientConstant_coeff_46
  recurrence2QuotientConstant_coeff_47
  recurrence2QuotientConstant_coeff_48
  recurrence2QuotientConstant_coeff_49
  recurrence2QuotientConstant_coeff_50
  recurrence2QuotientConstant_coeff_51
  recurrence2QuotientConstant_coeff_52
  recurrence2QuotientConstant_coeff_53
  recurrence2QuotientConstant_coeff_54
  recurrence2QuotientConstant_coeff_55
  recurrence2QuotientConstant_coeff_56
  recurrence2QuotientConstant_coeff_57
  recurrence2QuotientConstant_coeff_58
  recurrence2QuotientConstant_coeff_59
  recurrence2QuotientConstant_coeff_60
  recurrence2QuotientConstant_coeff_61
  recurrence2QuotientConstant_coeff_62
  recurrence2QuotientConstant_coeff_63
  recurrence2QuotientConstant_coeff_64
  recurrence2QuotientConstant_coeff_65
  recurrence2QuotientConstant_coeff_66
  recurrence2QuotientConstant_coeff_67
  recurrence2QuotientConstant_coeff_68
  recurrence2QuotientConstant_coeff_69
  recurrence2QuotientConstant_coeff_70
  recurrence2QuotientConstant_coeff_71
  recurrence2QuotientConstant_coeff_72
  recurrence2QuotientConstant_coeff_73
  recurrence2QuotientConstant_coeff_74
  recurrence2QuotientConstant_coeff_75
  recurrence2QuotientConstant_coeff_76
  recurrence2QuotientConstant_coeff_77
  recurrence2QuotientConstant_coeff_78
  recurrence2QuotientConstant_coeff_79
  recurrence2QuotientConstant_coeff_80
  recurrence2QuotientConstant_coeff_81
  recurrence2QuotientConstant_coeff_82
  recurrence2QuotientConstant_coeff_83
  recurrence2QuotientConstant_coeff_84
  recurrence2QuotientConstant_coeff_85
  recurrence2QuotientConstant_coeff_86
  recurrence2QuotientConstant_coeff_87
  recurrence2QuotientConstant_coeff_88
  recurrence2QuotientConstant_coeff_89
  recurrence2QuotientConstant_coeff_90
  recurrence2QuotientConstant_coeff_91
  recurrence2QuotientConstant_coeff_92
  recurrence2QuotientConstant_coeff_93
  recurrence2QuotientConstant_coeff_94
  recurrence2QuotientConstant_coeff_95
  recurrence2QuotientConstant_coeff_96
  recurrence2QuotientConstant_coeff_97
  recurrence2QuotientConstant_coeff_98
  recurrence2QuotientConstant_coeff_99
  recurrence2QuotientConstant_coeff_100
  recurrence2QuotientConstant_coeff_101
  recurrence2QuotientConstant_coeff_102
  recurrence2QuotientConstant_coeff_103
  recurrence2QuotientConstant_coeff_104
  recurrence2QuotientConstant_coeff_105
  recurrence2QuotientConstant_coeff_106
  recurrence2QuotientConstant_coeff_107
  recurrence2QuotientConstant_coeff_108
  recurrence2QuotientConstant_coeff_109
  recurrence2QuotientConstant_coeff_110
  recurrence2QuotientConstant_coeff_111
  recurrence2QuotientConstant_coeff_112
  recurrence2QuotientConstant_coeff_113
  recurrence2QuotientConstant_coeff_114
  recurrence2QuotientConstant_coeff_115
  recurrence2QuotientConstant_coeff_116
  recurrence2QuotientConstant_coeff_117
  recurrence2QuotientConstant_coeff_118
  recurrence2QuotientConstant_coeff_119
  recurrence2QuotientConstant_coeff_120
  recurrence2QuotientConstant_coeff_121
  recurrence2QuotientConstant_coeff_122
  recurrence2QuotientConstant_coeff_123
  recurrence2QuotientConstant_coeff_124
  recurrence2QuotientConstant_coeff_125
  recurrence2QuotientConstant_coeff_126
  recurrence2QuotientConstant_coeff_127
  recurrence2QuotientConstant_coeff_128
  recurrence2QuotientConstant_coeff_129
  recurrence2QuotientConstant_coeff_130
  recurrence2QuotientConstant_coeff_131
  recurrence2QuotientConstant_coeff_132
  recurrence2QuotientConstant_coeff_133
  recurrence2QuotientConstant_coeff_134
  recurrence2QuotientConstant_coeff_135
  recurrence2QuotientConstant_coeff_136
  recurrence2QuotientConstant_coeff_137
  recurrence2QuotientConstant_coeff_138
  recurrence2QuotientConstant_coeff_139
  recurrence2QuotientConstant_coeff_140
  recurrence2QuotientConstant_coeff_141
  recurrence2QuotientConstant_coeff_142
  recurrence2QuotientConstant_coeff_143
  recurrence2QuotientConstant_coeff_144
  recurrence2QuotientConstant_coeff_145
  recurrence2QuotientConstant_coeff_146
  recurrence2QuotientConstant_coeff_147
  recurrence2QuotientConstant_coeff_148
  recurrence2QuotientConstant_coeff_149
  recurrence2QuotientConstant_coeff_150
  recurrence2QuotientConstant_coeff_151
  recurrence2QuotientConstant_coeff_152
  recurrence2QuotientConstant_coeff_153
  recurrence2QuotientConstant_coeff_154
  recurrence2QuotientConstant_coeff_155
  recurrence2QuotientConstant_coeff_156
  recurrence2QuotientConstant_coeff_157
  recurrence2QuotientConstant_coeff_158
  recurrence2QuotientConstant_coeff_159
  recurrence2QuotientConstant_coeff_160
  recurrence2QuotientConstant_coeff_161
  recurrence2QuotientConstant_coeff_162
  recurrence2QuotientConstant_coeff_163
  recurrence2QuotientConstant_coeff_164
  recurrence2QuotientConstant_coeff_165
  recurrence2QuotientConstant_coeff_166
  recurrence2QuotientConstant_coeff_167
  recurrence2QuotientConstant_coeff_168
  recurrence2QuotientConstant_coeff_169
  recurrence2QuotientConstant_coeff_170
  recurrence2QuotientConstant_coeff_171
  recurrence2QuotientConstant_coeff_172
  recurrence2QuotientConstant_coeff_173
  recurrence2QuotientConstant_coeff_174
  recurrence2QuotientConstant_coeff_175
  recurrence2QuotientConstant_coeff_176
  recurrence2QuotientConstant_coeff_177
  recurrence2QuotientConstant_coeff_178
  recurrence2QuotientConstant_coeff_179
  recurrence2QuotientConstant_coeff_180
  recurrence2QuotientConstant_coeff_181
  recurrence2QuotientConstant_coeff_182
  recurrence2QuotientConstant_coeff_183
  recurrence2QuotientConstant_coeff_184
  recurrence2QuotientConstant_coeff_185
  recurrence2QuotientConstant_coeff_186
  recurrence2QuotientConstant_coeff_187
  recurrence2QuotientConstant_coeff_188
  recurrence2QuotientConstant_coeff_189
  recurrence2QuotientConstant_coeff_190
  recurrence2QuotientConstant_coeff_191
  recurrence2QuotientConstant_coeff_192
  recurrence2QuotientConstant_coeff_193
  recurrence2QuotientConstant_coeff_194
  recurrence2QuotientConstant_coeff_195
  recurrence2QuotientConstant_coeff_196
  recurrence2QuotientConstant_coeff_197
  recurrence2QuotientConstant_coeff_198
  recurrence2QuotientConstant_coeff_199
  recurrence2QuotientConstant_coeff_200
  recurrence2QuotientConstant_coeff_201
  recurrence2QuotientConstant_coeff_202
  recurrence2QuotientConstant_coeff_203
  recurrence2QuotientConstant_coeff_204
  recurrence2QuotientConstant_coeff_205
  recurrence2QuotientConstant_coeff_206
  recurrence2QuotientConstant_coeff_207
  recurrence2QuotientConstant_coeff_208
  recurrence2QuotientConstant_coeff_209
  recurrence2QuotientConstant_coeff_210
  recurrence2QuotientConstant_coeff_211
  recurrence2QuotientConstant_coeff_212
  recurrence2QuotientConstant_coeff_213
  recurrence2QuotientConstant_coeff_214
  recurrence2QuotientConstant_coeff_215
  recurrence2QuotientConstant_coeff_216
  recurrence2QuotientConstant_coeff_217
  recurrence2QuotientConstant_coeff_218
  recurrence2QuotientConstant_coeff_219
  recurrence2QuotientConstant_coeff_220
  recurrence2QuotientConstant_coeff_221
  recurrence2QuotientConstant_coeff_222
  recurrence2QuotientConstant_coeff_223
  recurrence2QuotientConstant_coeff_224
  recurrence2QuotientConstant_coeff_225
  recurrence2QuotientConstant_coeff_226
  recurrence2QuotientConstant_coeff_227
  recurrence2QuotientConstant_coeff_228
  recurrence2QuotientConstant_coeff_229
  recurrence2QuotientConstant_coeff_230
  recurrence2QuotientConstant_coeff_231
  recurrence2QuotientConstant_coeff_232
  recurrence2QuotientConstant_coeff_233

private theorem recurrence2Scalar4Main_coeff_233_suffix_zero :
    (∑ x ∈ Finset.range 95,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (233 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_233 :
    recurrence2Scalar4Main.coeff 233 =
      ((((2 * 10 ^ 70 +
        5057327041114049748727115200318705275604219425774483380243344447416469) * 10 ^ 70 +
        7976960140402595815960747700337511381261661001724427582813933767201133) * 10 ^ 70 +
        9661657792775985574807797244229569410629980805620198196598865515037903) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 234 = 0 +
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
    rw [show 106 = 11 +
      95 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_233_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_234_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (234 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (234 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_234_suffix_zero :
    (∑ x ∈ Finset.range 96,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (234 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_234 :
    recurrence2Scalar4Main.coeff 234 =
      -((((2 * 10 ^ 70 +
        2871626586340419799051821632226804390158489202336449304145904112507447) * 10 ^ 70 +
        3315491754232813452129111558310529182485291173048651998110841942925901) * 10 ^ 70 +
        4478908444473150495383945090668640817178841179764994982701578537347509) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 106 = 10 +
      96 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_234_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_234_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_235_prefix_zero :
    (∑ x ∈ Finset.range 2,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (235 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (235 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_235_suffix_zero :
    (∑ x ∈ Finset.range 97,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (235 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_235 :
    recurrence2Scalar4Main.coeff 235 =
      ((((1 * 10 ^ 70 +
        9340580889144803740619239846202873320532156981010622271396772677727976) * 10 ^ 70 +
        2845681816180731094463493557888206239499274508955980123288363232152193) * 10 ^ 70 +
        3527609430417298413517241187396633249172081259795413923536298274313873) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 236 = 2 +
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
    rw [show 106 = 9 +
      97 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_235_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_235_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_236_prefix_zero :
    (∑ x ∈ Finset.range 3,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (236 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (236 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_236_suffix_zero :
    (∑ x ∈ Finset.range 98,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (236 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_236 :
    recurrence2Scalar4Main.coeff 236 =
      -((((1 * 10 ^ 70 +
        4813222249161520022515097989814886675980574111494011698786755566714103) * 10 ^ 70 +
        1057759198559243826106667402134548158004581776065774406197211719777707) * 10 ^ 70 +
        6081050922343524892745915900748796712459117680641636279978490331670013) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 237 = 3 +
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
    rw [show 106 = 8 +
      98 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_236_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_236_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_237_prefix_zero :
    (∑ x ∈ Finset.range 4,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (237 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (237 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_237_suffix_zero :
    (∑ x ∈ Finset.range 99,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (237 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_237 :
    recurrence2Scalar4Main.coeff 237 =
      (((9757267909238146691725805794034231007857518492657073064713666088481184 * 10 ^ 70 +
        2988935472459700023731527596718774960612944137671374498738210705751160) * 10 ^ 70 +
        6325407740643900445367110834182473223077386418415527396020941104428197) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 238 = 4 +
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
    rw [show 106 = 7 +
      99 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_237_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_237_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_238_prefix_zero :
    (∑ x ∈ Finset.range 5,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (238 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (238 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_238_suffix_zero :
    (∑ x ∈ Finset.range 100,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (238 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_238 :
    recurrence2Scalar4Main.coeff 238 =
      -(((4682728251802342731016313121774157820511009557814972145284574441846154 * 10 ^ 70 +
        7318041728853255985014879879394517075401401915705586780541825540663314) * 10 ^ 70 +
        4270156164956538308364238173399694049475247600970711443267101282428110) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 239 = 5 +
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
    rw [show 106 = 6 +
      100 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_238_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_238_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_239_prefix_zero :
    (∑ x ∈ Finset.range 6,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (239 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (239 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_239_suffix_zero :
    (∑ x ∈ Finset.range 101,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (239 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_239 :
    recurrence2Scalar4Main.coeff 239 =
      (((61748796257815510421246412051399408222653137690219748412171341687230 * 10 ^ 70 +
        0924802750423147126588062730447554368661137966891056599496614430757209) * 10 ^ 70 +
        5989207753041590226451371923976600515455844711615400014415983117421633) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 240 = 6 +
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
    rw [show 106 = 5 +
      101 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_239_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_239_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_240_prefix_zero :
    (∑ x ∈ Finset.range 7,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (240 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (240 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_240_suffix_zero :
    (∑ x ∈ Finset.range 102,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (240 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_240 :
    recurrence2Scalar4Main.coeff 240 =
      (((3738664958035079709476863232766116506872591729057223985461035779771939 * 10 ^ 70 +
        5396833779835954650556511224033733810968181453575386717539220945160974) * 10 ^ 70 +
        3113630150550106907159338226820304017162548546731770390764400100763789) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 241 = 7 +
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
    rw [show 106 = 4 +
      102 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_240_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_240_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_241_prefix_zero :
    (∑ x ∈ Finset.range 8,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (241 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (241 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_241_suffix_zero :
    (∑ x ∈ Finset.range 103,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (241 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_241 :
    recurrence2Scalar4Main.coeff 241 =
      -(((6498643732584501641217682538080534716429929280450152232545971052218296 * 10 ^ 70 +
        0827262118672688806973524598626311429724259576989410080253548548669141) * 10 ^ 70 +
        3155689726407035693706851201286915007033504705083113535286719449867176) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 242 = 8 +
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
    rw [show 106 = 3 +
      103 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_241_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_241_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_242_prefix_zero :
    (∑ x ∈ Finset.range 9,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (242 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (242 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_242_suffix_zero :
    (∑ x ∈ Finset.range 104,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (242 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_242 :
    recurrence2Scalar4Main.coeff 242 =
      (((8156732864852994302321558781057420058571793415885866955804940754587738 * 10 ^ 70 +
        4545736834011248388916724411814000666178550823271089487421134845274311) * 10 ^ 70 +
        5280766023891608928563737744434928286322591221333633909396133572194752) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 243 = 9 +
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
    rw [show 106 = 2 +
      104 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_242_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_242_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_243_prefix_zero :
    (∑ x ∈ Finset.range 10,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (243 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (243 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_243_suffix_zero :
    (∑ x ∈ Finset.range 105,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (243 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_243 :
    recurrence2Scalar4Main.coeff 243 =
      -(((8792503298743527171160736932522884589964650048071381744082426214533600 * 10 ^ 70 +
        1189984250901718257227121854171774944002982255808239644413259205401778) * 10 ^ 70 +
        4300600138488815840078203010088240114019525249247298736425581592901577) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 244 = 10 +
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
    rw [show 106 = 1 +
      105 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_243_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_243_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_244_prefix_zero :
    (∑ x ∈ Finset.range 11,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (244 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (244 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_244_suffix_zero :
    (∑ x ∈ Finset.range 106,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (244 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_244 :
    recurrence2Scalar4Main.coeff 244 =
      (((8588495995472722315772285571091482295007062688634599267402870804101743 * 10 ^ 70 +
        8798819117019430611580180423043755243631730399018831074305040198061234) * 10 ^ 70 +
        8100937997709316720862002533669005920634832900586036890589058070975142) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 245 = 11 +
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
  rw [recurrence2Scalar4Main_coeff_244_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_244_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_245_prefix_zero :
    (∑ x ∈ Finset.range 12,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (245 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (245 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_245_suffix_zero :
    (∑ x ∈ Finset.range 107,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (245 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_245 :
    recurrence2Scalar4Main.coeff 245 =
      -(((7782574146567904921831825077969432401880110868161894806657449746305046 * 10 ^ 70 +
        8544964579477549768547894847059329385960382091432644066840493935788021) * 10 ^ 70 +
        3658206066710007627277156628794173802674437931789930203137073376187324) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 246 = 12 +
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
    rw [show 138 = 31 +
      107 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_245_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_245_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_246_prefix_zero :
    (∑ x ∈ Finset.range 13,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (246 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (246 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_246_suffix_zero :
    (∑ x ∈ Finset.range 108,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (246 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_246 :
    recurrence2Scalar4Main.coeff 246 =
      (((6621648860206775958950719896940714272759502169063566390793938318315170 * 10 ^ 70 +
        8894142415421182517420044799066692114551015193846898975195660775242751) * 10 ^ 70 +
        1472456342563357817488812595511786961815254858192502791209386628723553) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 247 = 13 +
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
    rw [show 138 = 30 +
      108 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_246_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_246_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_247_prefix_zero :
    (∑ x ∈ Finset.range 14,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (247 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (247 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_247_suffix_zero :
    (∑ x ∈ Finset.range 109,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (247 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_247 :
    recurrence2Scalar4Main.coeff 247 =
      -(((5325094848585737509117423149084217047628969015939737292470241774968613 * 10 ^ 70 +
        2664045550265553451366319768519072104678813879070703938001475734279360) * 10 ^ 70 +
        2712835893403210076795755600045215606120419323748660579296258663675014) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 248 = 14 +
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
    rw [show 138 = 29 +
      109 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_247_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_247_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_248_prefix_zero :
    (∑ x ∈ Finset.range 15,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (248 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (248 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_248_suffix_zero :
    (∑ x ∈ Finset.range 110,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (248 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_248 :
    recurrence2Scalar4Main.coeff 248 =
      (((4062197538505271766502390226753265459656479018318820546045166033328825 * 10 ^ 70 +
        1874632216477678241463252837018652509886575493508897130908928120623986) * 10 ^ 70 +
        7587600705644551005203577860166204347176381371191368882280386437875061) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 249 = 15 +
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
    rw [show 138 = 28 +
      110 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_248_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_248_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_249_prefix_zero :
    (∑ x ∈ Finset.range 16,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (249 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (249 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_249_suffix_zero :
    (∑ x ∈ Finset.range 111,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (249 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_249 :
    recurrence2Scalar4Main.coeff 249 =
      -(((2943978365596124189120952559595812440888742705636730322595077179388766 * 10 ^ 70 +
        0049049003019588345405432080222996238457107202032639569495495340298373) * 10 ^ 70 +
        8387258755346882762954649019159399027670215721800979434777258503341089) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 250 = 16 +
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
    rw [show 138 = 27 +
      111 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_249_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_249_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_250_prefix_zero :
    (∑ x ∈ Finset.range 17,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (250 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (250 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_250_suffix_zero :
    (∑ x ∈ Finset.range 112,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (250 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_250 :
    recurrence2Scalar4Main.coeff 250 =
      (((2026726229206241035645933191303456762709510557291716601172434074567892 * 10 ^ 70 +
        2304969848137410935615323197278048254200114911849375691075692803653404) * 10 ^ 70 +
        4152283039884669680007358715807722387004423959236479106479714533605337) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 251 = 17 +
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
    rw [show 138 = 26 +
      112 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_250_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_250_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_251_prefix_zero :
    (∑ x ∈ Finset.range 18,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (251 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (251 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_251_suffix_zero :
    (∑ x ∈ Finset.range 113,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (251 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_251 :
    recurrence2Scalar4Main.coeff 251 =
      -(((1322995224996848288132936829843958676897036195564653980357456661234488 * 10 ^ 70 +
        0470477637762095115299162799720997993022920295211180591239294367811115) * 10 ^ 70 +
        0552509675163172687111342924661882045084600954932271847318984712757701) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 252 = 18 +
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
    rw [show 138 = 25 +
      113 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_251_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_251_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_252_prefix_zero :
    (∑ x ∈ Finset.range 19,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (252 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (252 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_252_suffix_zero :
    (∑ x ∈ Finset.range 114,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (252 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_252 :
    recurrence2Scalar4Main.coeff 252 =
      (((815670964880634805934652467821992919613451842488111359134564563903940 * 10 ^ 70 +
        4762893610479595023434483777873863088283930257197982119173133287852682) * 10 ^ 70 +
        6820806079894605453422921146491605728751729137097837946277286199067356) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 253 = 19 +
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
    rw [show 138 = 24 +
      114 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_252_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_252_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_253_prefix_zero :
    (∑ x ∈ Finset.range 20,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (253 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (253 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_253_suffix_zero :
    (∑ x ∈ Finset.range 115,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (253 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_253 :
    recurrence2Scalar4Main.coeff 253 =
      -(((471562963904417405795405211654924089981323000392068654751242593940905 * 10 ^ 70 +
        8618264794686646602694887048771058319841102137616094955804495058974942) * 10 ^ 70 +
        3097871432170364679141165033208145221987983146892505159822642759348293) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 254 = 20 +
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
    rw [show 138 = 23 +
      115 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_253_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_253_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_254_prefix_zero :
    (∑ x ∈ Finset.range 21,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (254 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (254 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_254_suffix_zero :
    (∑ x ∈ Finset.range 116,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (254 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_254 :
    recurrence2Scalar4Main.coeff 254 =
      (((252314936813368497195438720492528360960868720976288672901623186034958 * 10 ^ 70 +
        4381196934744636746341934480780383274106796102059843078316288814217715) * 10 ^ 70 +
        7487852164598079830872113007897766178534970089757387536367426871662421) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 255 = 21 +
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
    rw [show 138 = 22 +
      116 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_254_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_254_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_255_prefix_zero :
    (∑ x ∈ Finset.range 22,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (255 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (255 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_255_suffix_zero :
    (∑ x ∈ Finset.range 117,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (255 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_255 :
    recurrence2Scalar4Main.coeff 255 =
      -(((121759503221010459329646078505479551556973205866379900759862738370209 * 10 ^ 70 +
        6524505682524590607518382983637798213475415155328096794064570310569835) * 10 ^ 70 +
        5269468138841201891136495409657823545039563910456841430865924868702220) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 256 = 22 +
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
    rw [show 138 = 21 +
      117 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_255_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_255_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_256_prefix_zero :
    (∑ x ∈ Finset.range 23,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (256 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (256 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_256_suffix_zero :
    (∑ x ∈ Finset.range 118,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (256 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_256 :
    recurrence2Scalar4Main.coeff 256 =
      (((49867196691105694092177311588667815558824006320550828971751876906966 * 10 ^ 70 +
        9853876314145134769912460959933046888352911370528159329641791972125539) * 10 ^ 70 +
        5875903170568847880335730946162732908860890984454919179696251800964341) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 257 = 23 +
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
    rw [show 138 = 20 +
      118 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_256_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_256_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_257_prefix_zero :
    (∑ x ∈ Finset.range 24,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (257 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (257 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_257_suffix_zero :
    (∑ x ∈ Finset.range 119,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (257 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_257 :
    recurrence2Scalar4Main.coeff 257 =
      -(((14032551848324608583738555497190769123399987994810644416469534358012 * 10 ^ 70 +
        7595516643083006566694767056673811432669592894336594211764222742733803) * 10 ^ 70 +
        7723293730861852927781849005881823257727646628223846942485075877988839) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 258 = 24 +
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
    rw [show 138 = 19 +
      119 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_257_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_257_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_258_prefix_zero :
    (∑ x ∈ Finset.range 25,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (258 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (258 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_258_suffix_zero :
    (∑ x ∈ Finset.range 120,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (258 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_258 :
    recurrence2Scalar4Main.coeff 258 =
      -(((1364023018918583943348982890060612097670685989474426096329249333825 * 10 ^ 70 +
        8382021314911917069695413432931386184362814950702490366438526192991711) * 10 ^ 70 +
        3906345757078972131554976241816869336647083313040678932758773580908522) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 259 = 25 +
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
    rw [show 138 = 18 +
      120 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_258_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_258_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_259_prefix_zero :
    (∑ x ∈ Finset.range 26,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (259 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (259 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_259_suffix_zero :
    (∑ x ∈ Finset.range 121,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (259 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_259 :
    recurrence2Scalar4Main.coeff 259 =
      (((6262678930443496151115965834328334048569471172112235364066791425843 * 10 ^ 70 +
        9680858301833019606512120721555106717022795419288683352676573558756635) * 10 ^ 70 +
        3102719228919099889341804714405030033034097985924953078905208084506396) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 260 = 26 +
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
    rw [show 138 = 17 +
      121 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_259_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_259_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_260_prefix_zero :
    (∑ x ∈ Finset.range 27,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (260 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (260 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_260_suffix_zero :
    (∑ x ∈ Finset.range 122,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (260 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_260 :
    recurrence2Scalar4Main.coeff 260 =
      -(((6466967141381333246787980441798992966569616507802960249583921296073 * 10 ^ 70 +
        9606122424613101208716302252422342169268387711865263400974826599468515) * 10 ^ 70 +
        2676021280874677120133562785536825686477512245187653689173118937331312) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 261 = 27 +
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
    rw [show 138 = 16 +
      122 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_260_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_260_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_261_prefix_zero :
    (∑ x ∈ Finset.range 28,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (261 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (261 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_261_suffix_zero :
    (∑ x ∈ Finset.range 123,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (261 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_261 :
    recurrence2Scalar4Main.coeff 261 =
      (((5043671314002169760071889092046459285767620760973052532232432161677 * 10 ^ 70 +
        2010651031140962690649921963235542100251001163773799410661902511772332) * 10 ^ 70 +
        8095721707351994219058872330411554014846936773778292964389401110444430) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 262 = 28 +
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
    rw [show 138 = 15 +
      123 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_261_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_261_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_262_prefix_zero :
    (∑ x ∈ Finset.range 29,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (262 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (262 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_262_suffix_zero :
    (∑ x ∈ Finset.range 124,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (262 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_262 :
    recurrence2Scalar4Main.coeff 262 =
      -(((3411735983611044006562077705574801142488066965158784086771254753815 * 10 ^ 70 +
        8489774757661790301452396601430545311256217612940401645021331140635002) * 10 ^ 70 +
        7113222151514425736206113326178053243895602617665295849225799464559980) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 263 = 29 +
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
    rw [show 138 = 14 +
      124 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_262_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_262_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_263_prefix_zero :
    (∑ x ∈ Finset.range 30,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (263 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (263 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_263_suffix_zero :
    (∑ x ∈ Finset.range 125,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (263 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_263 :
    recurrence2Scalar4Main.coeff 263 =
      (((2095315015948059169872687107279616683503135097509927504463696871716 * 10 ^ 70 +
        2886847528605335495213413379118857939632023817815886257685958113451165) * 10 ^ 70 +
        7846289452102579455288271023447825637470169102012693363576455771498696) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 264 = 30 +
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
    rw [show 138 = 13 +
      125 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_263_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_263_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_264_prefix_zero :
    (∑ x ∈ Finset.range 31,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (264 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (264 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_264_suffix_zero :
    (∑ x ∈ Finset.range 126,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (264 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_264 :
    recurrence2Scalar4Main.coeff 264 =
      -(((1192139986631023859330296253487633727250280537834422015071792367148 * 10 ^ 70 +
        1481848206985932379417117755954403297408416071244559766141995450767882) * 10 ^ 70 +
        5094989074090946124189403487964693917032336869225924592497232340771334) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 265 = 31 +
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
    rw [show 138 = 12 +
      126 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_264_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_264_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_265_prefix_zero :
    (∑ x ∈ Finset.range 32,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (265 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (265 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_265_suffix_zero :
    (∑ x ∈ Finset.range 127,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (265 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_265 :
    recurrence2Scalar4Main.coeff 265 =
      (((634635409849251197252747616968198795321261972963433155669543349459 * 10 ^ 70 +
        6203590572736926329390252656042868923978113836510429440849890814921840) * 10 ^ 70 +
        0271149425108542464113839405616898112205126648179369759758826077889102) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 266 = 32 +
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
    rw [show 138 = 11 +
      127 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_265_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_265_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_266_prefix_zero :
    (∑ x ∈ Finset.range 33,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (266 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (266 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_266_suffix_zero :
    (∑ x ∈ Finset.range 128,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (266 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_266 :
    recurrence2Scalar4Main.coeff 266 =
      -(((317611099001948136142878680941308194993580611913547799749593038370 * 10 ^ 70 +
        9839386553638383524900601950811247963978334708700152936223766711629260) * 10 ^ 70 +
        4649819905411082480129689626959650086957754075730438523447190186022983) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 267 = 33 +
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
    rw [show 138 = 10 +
      128 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_266_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_266_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_267_prefix_zero :
    (∑ x ∈ Finset.range 34,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (267 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (267 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_267_suffix_zero :
    (∑ x ∈ Finset.range 129,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (267 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_267 :
    recurrence2Scalar4Main.coeff 267 =
      (((149643403312512881273207728029641289395449108249662062879769192747 * 10 ^ 70 +
        1495441376151969292904050149616225616122426927462936542446724078758567) * 10 ^ 70 +
        8490476222084507387200631337834464341394705334039122013122028493380360) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 268 = 34 +
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
    rw [show 138 = 9 +
      129 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_267_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_267_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_268_prefix_zero :
    (∑ x ∈ Finset.range 35,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (268 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (268 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_268_suffix_zero :
    (∑ x ∈ Finset.range 130,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (268 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_268 :
    recurrence2Scalar4Main.coeff 268 =
      -(((66287945208503764729927818731334654973355968570954959720745401163 * 10 ^ 70 +
        6499524863012603374682231741806487753119567926258388433270100583686409) * 10 ^ 70 +
        4510018576983410213981458709916533485803226287319779499012152213944933) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 269 = 35 +
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
    rw [show 138 = 8 +
      130 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_268_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_268_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_269_prefix_zero :
    (∑ x ∈ Finset.range 36,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (269 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (269 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_269_suffix_zero :
    (∑ x ∈ Finset.range 131,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (269 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_269 :
    recurrence2Scalar4Main.coeff 269 =
      (((27486905798516777385799742377870791056146260961866161020510674035 * 10 ^ 70 +
        3295720340485389510083865323994111177520792102529098210602344624430995) * 10 ^ 70 +
        5625220617353607422905597561746561624414584105826455299702165982909718) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 270 = 36 +
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
    rw [show 138 = 7 +
      131 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_269_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_269_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_270_prefix_zero :
    (∑ x ∈ Finset.range 37,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (270 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (270 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_270_suffix_zero :
    (∑ x ∈ Finset.range 132,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (270 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_270 :
    recurrence2Scalar4Main.coeff 270 =
      -(((10575273548513555416584256346111190868456920682417890338762202857 * 10 ^ 70 +
        6576253338217960014411829882407364307055900984214257050548313923433624) * 10 ^ 70 +
        2720751778545240738074699619914629629295066977357919536893305808553716) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 271 = 37 +
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
    rw [show 138 = 6 +
      132 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_270_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_270_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_271_prefix_zero :
    (∑ x ∈ Finset.range 38,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (271 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (271 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_271_suffix_zero :
    (∑ x ∈ Finset.range 133,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (271 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_271 :
    recurrence2Scalar4Main.coeff 271 =
      (((3711228644286223140144035132784779708922645238481233672408901240 * 10 ^ 70 +
        5052519771260707012721656181183365883522119005902099390362797117927696) * 10 ^ 70 +
        0763649773226656004060105182899577074887663573208331752787583856617404) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 272 = 38 +
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
    rw [show 138 = 5 +
      133 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_271_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_271_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_272_prefix_zero :
    (∑ x ∈ Finset.range 39,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (272 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (272 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_272_suffix_zero :
    (∑ x ∈ Finset.range 134,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (272 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_272 :
    recurrence2Scalar4Main.coeff 272 =
      -(((1145850305959248571582202941059111594230226079855253392875722286 * 10 ^ 70 +
        5713249991199885863890831803092537351125633960299370602946064637884697) * 10 ^ 70 +
        3387933188081268549785817593780228112683235624098896230139940455162537) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 273 = 39 +
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
    rw [show 138 = 4 +
      134 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_272_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_272_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_273_prefix_zero :
    (∑ x ∈ Finset.range 40,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (273 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (273 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_273_suffix_zero :
    (∑ x ∈ Finset.range 135,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (273 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_273 :
    recurrence2Scalar4Main.coeff 273 =
      (((282708832902101179153294249089823445629032970073173567543875333 * 10 ^ 70 +
        1214170589308249685905789220088164304584446292142754368922400115651098) * 10 ^ 70 +
        7467886013733849512983854352689214016392321564848814974051130928586832) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 274 = 40 +
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
    rw [show 138 = 3 +
      135 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_273_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_273_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_274_prefix_zero :
    (∑ x ∈ Finset.range 41,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (274 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (274 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_274_suffix_zero :
    (∑ x ∈ Finset.range 136,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (274 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_274 :
    recurrence2Scalar4Main.coeff 274 =
      -(((34464527789539916165323392611836997957220661492336873789250520 * 10 ^ 70 +
        9625613609201197627868447455425211938410627165291443985147862295736486) * 10 ^ 70 +
        6200055063218009895021986213535616109689019639941904498051757721216705) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 275 = 41 +
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
    rw [show 138 = 2 +
      136 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_274_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_274_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_275_prefix_zero :
    (∑ x ∈ Finset.range 42,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (275 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (275 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_275_suffix_zero :
    (∑ x ∈ Finset.range 137,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (275 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_275 :
    recurrence2Scalar4Main.coeff 275 =
      -(((17319025889175851267218917754273793184338961852276718784443985 * 10 ^ 70 +
        2119688698401509642351168750449846175736417971124351761937399245182587) * 10 ^ 70 +
        1593056784287150164399359508686329758496249605491939623077235429106773) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 276 = 42 +
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
    rw [show 138 = 1 +
      137 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_275_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_275_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_276_prefix_zero :
    (∑ x ∈ Finset.range 43,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (276 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (276 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_276_suffix_zero :
    (∑ x ∈ Finset.range 138,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (276 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_276 :
    recurrence2Scalar4Main.coeff 276 =
      (((17781823741330638633209656980049432907780789698769866532031069 * 10 ^ 70 +
        8210028370982633294501594156222923525078001948571868338463393339588442) * 10 ^ 70 +
        4797923400163356950840157448073689163553380258298173484130008725284483) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 277 = 43 +
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
  rw [recurrence2Scalar4Main_coeff_276_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_276_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_277_prefix_zero :
    (∑ x ∈ Finset.range 44,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (277 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (277 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_277_suffix_zero :
    (∑ x ∈ Finset.range 139,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (277 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_277 :
    recurrence2Scalar4Main.coeff 277 =
      -(((10356217667325574711841560682776530693636594194467623585579075 * 10 ^ 70 +
        5291570372563097204580906168642411205090768971941130709675675590660737) * 10 ^ 70 +
        9022942898225087710458140692577810156121453628648379600991864830331174) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 278 = 44 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 31 +
      139 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_277_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_277_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_278_prefix_zero :
    (∑ x ∈ Finset.range 45,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (278 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (278 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_278_suffix_zero :
    (∑ x ∈ Finset.range 140,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (278 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_278 :
    recurrence2Scalar4Main.coeff 278 =
      (((4894333509368446461604349756026751296445129582925017519544610 * 10 ^ 70 +
        3726189942181627528421298955531896781364573874317051642435577644801849) * 10 ^ 70 +
        8214778980672674737583008812056683704954560693872655941972759980410064) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 279 = 45 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 30 +
      140 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_278_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_278_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_279_prefix_zero :
    (∑ x ∈ Finset.range 46,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (279 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (279 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_279_suffix_zero :
    (∑ x ∈ Finset.range 141,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (279 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_279 :
    recurrence2Scalar4Main.coeff 279 =
      -(((2034817319694488991691844887174589353583176746333182112508700 * 10 ^ 70 +
        7408394199228265036076009388985551393981894908634978933257316594742343) * 10 ^ 70 +
        8346780175385474431791119385364604038016870454950021761054646382686679) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 280 = 46 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 29 +
      141 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_279_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_279_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_280_prefix_zero :
    (∑ x ∈ Finset.range 47,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (280 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (280 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_280_suffix_zero :
    (∑ x ∈ Finset.range 142,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (280 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_280 :
    recurrence2Scalar4Main.coeff 280 =
      (((766814019202240837495517632432051705725908196972246707966048 * 10 ^ 70 +
        6888400034931052297028974290990730859807973568183003774144506885198824) * 10 ^ 70 +
        1866519301625429256491377942097184247595302924687512620495951769536357) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 281 = 47 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 28 +
      142 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_280_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_280_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_281_prefix_zero :
    (∑ x ∈ Finset.range 48,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (281 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (281 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_281_suffix_zero :
    (∑ x ∈ Finset.range 143,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (281 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_281 :
    recurrence2Scalar4Main.coeff 281 =
      -(((265213349982371630872809716026178589521837653186980370757346 * 10 ^ 70 +
        2493432871721930427124780604485499143222579628440707433269193896655196) * 10 ^ 70 +
        5426459551107716958509988911736886938726180806846214239355287867494243) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 282 = 48 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 27 +
      143 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_281_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_281_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_282_prefix_zero :
    (∑ x ∈ Finset.range 49,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (282 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (282 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_282_suffix_zero :
    (∑ x ∈ Finset.range 144,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (282 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_282 :
    recurrence2Scalar4Main.coeff 282 =
      (((84507646117770353885872582958484834119963387379532519484221 * 10 ^ 70 +
        3087852766447466602448697811057035632309083035645050888106020363574738) * 10 ^ 70 +
        8974526397248147507712673209180428853616637720380196100347768987304302) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 283 = 49 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 26 +
      144 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_282_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_282_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_283_prefix_zero :
    (∑ x ∈ Finset.range 50,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (283 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (283 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_283_suffix_zero :
    (∑ x ∈ Finset.range 145,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (283 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_283 :
    recurrence2Scalar4Main.coeff 283 =
      -(((24747135869643876869901891447028519444556606846903135495662 * 10 ^ 70 +
        5690433110418223492039389224796847808690111558921519029459270760263484) * 10 ^ 70 +
        3541832255945240655887835453968185988076900638612685772908281595257072) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 284 = 50 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 25 +
      145 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_283_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_283_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_284_prefix_zero :
    (∑ x ∈ Finset.range 51,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (284 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (284 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_284_suffix_zero :
    (∑ x ∈ Finset.range 146,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (284 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_284 :
    recurrence2Scalar4Main.coeff 284 =
      (((6596740220743624507626170913878684354510334514440135467900 * 10 ^ 70 +
        2285859548087090156150013901379737019408480341030282703752625159589804) * 10 ^ 70 +
        3521843687416352928718363762367961702513711102918864507354658841583190) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 285 = 51 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 24 +
      146 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_284_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_284_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_285_prefix_zero :
    (∑ x ∈ Finset.range 52,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (285 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (285 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_285_suffix_zero :
    (∑ x ∈ Finset.range 147,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (285 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_285 :
    recurrence2Scalar4Main.coeff 285 =
      -(((1566248284354029531337690926235842213208070321419674628448 * 10 ^ 70 +
        0278712120040553479817523401954103443397032875374611215303331225505070) * 10 ^ 70 +
        8392877226635170747104255201667902055036361415168873448017228928368715) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 286 = 52 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 23 +
      147 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_285_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_285_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_286_prefix_zero :
    (∑ x ∈ Finset.range 53,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (286 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (286 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_286_suffix_zero :
    (∑ x ∈ Finset.range 148,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (286 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_286 :
    recurrence2Scalar4Main.coeff 286 =
      (((314584376353735512328870114421845726193586055643440364880 * 10 ^ 70 +
        0244451131171790564093026738530393859180083115577715043282353519221709) * 10 ^ 70 +
        1743768464277451827784340843082006591432609005515207993919542469619893) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 287 = 53 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 22 +
      148 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_286_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_286_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_287_prefix_zero :
    (∑ x ∈ Finset.range 54,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (287 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (287 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_287_suffix_zero :
    (∑ x ∈ Finset.range 149,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (287 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_287 :
    recurrence2Scalar4Main.coeff 287 =
      -(((45326758793160350902634340557608622878797578531836430802 * 10 ^ 70 +
        4911105763221192677737225306249293348747985593212201603980021342998143) * 10 ^ 70 +
        8138676864490298109542347627836061626166586574166691344230693817795205) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 288 = 54 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 21 +
      149 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_287_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_287_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_288_prefix_zero :
    (∑ x ∈ Finset.range 55,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (288 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (288 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_288_suffix_zero :
    (∑ x ∈ Finset.range 150,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (288 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_288 :
    recurrence2Scalar4Main.coeff 288 =
      (((248663128696351790295042424237721554408368955021838211 * 10 ^ 70 +
        0323307411702926437431655387971840732652135383312929883971260208367956) * 10 ^ 70 +
        7798705682242193315844971266266441979905203058133589507743407908413837) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 289 = 55 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 20 +
      150 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_288_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_288_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_289_prefix_zero :
    (∑ x ∈ Finset.range 56,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (289 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (289 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_289_suffix_zero :
    (∑ x ∈ Finset.range 151,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (289 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_289 :
    recurrence2Scalar4Main.coeff 289 =
      (((3024399911245546170609778986162330952309927214594705944 * 10 ^ 70 +
        6726423286541099161982213513430664967305697669459806465259116294113979) * 10 ^ 70 +
        4806288353140757701656673047171203712528153926240576464996583928440040) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 290 = 56 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 19 +
      151 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_289_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_289_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_290_prefix_zero :
    (∑ x ∈ Finset.range 57,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (290 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (290 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_290_suffix_zero :
    (∑ x ∈ Finset.range 152,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (290 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_290 :
    recurrence2Scalar4Main.coeff 290 =
      -(((1485337387794889519659904200086757043800942038105444238 * 10 ^ 70 +
        7585618425939533665908620485908226441934007477483096403543247987886044) * 10 ^ 70 +
        0662620087645451392723892025908365348369554624569814661977534873335070) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 291 = 57 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 18 +
      152 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_290_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_290_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_291_prefix_zero :
    (∑ x ∈ Finset.range 58,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (291 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (291 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_291_suffix_zero :
    (∑ x ∈ Finset.range 153,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (291 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_291 :
    recurrence2Scalar4Main.coeff 291 =
      (((512640590112788381664098899980367577939013818461451730 * 10 ^ 70 +
        6477420206182468920574201621126786065097153590660464662333807439007607) * 10 ^ 70 +
        2806782446549861343914022326604650020471025924216805870648576574811247) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 292 = 58 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 17 +
      153 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_291_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_291_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_292_prefix_zero :
    (∑ x ∈ Finset.range 59,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (292 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (292 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_292_suffix_zero :
    (∑ x ∈ Finset.range 154,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (292 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_292 :
    recurrence2Scalar4Main.coeff 292 =
      -(((147549368944646415226491759712302703181295602240855217 * 10 ^ 70 +
        1554605769333647273146131719760657592845813343209668169471535315860568) * 10 ^ 70 +
        3217360318782095041183012324890410636623802552305959996647914571376706) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 293 = 59 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 16 +
      154 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_292_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_292_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_293_prefix_zero :
    (∑ x ∈ Finset.range 60,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (293 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (293 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_293_suffix_zero :
    (∑ x ∈ Finset.range 155,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (293 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_293 :
    recurrence2Scalar4Main.coeff 293 =
      (((37176314550865123387151137297909298547861331780382565 * 10 ^ 70 +
        4789967781455788409626204994150901498743785001488405320558946206264247) * 10 ^ 70 +
        4536525867749845978876227748935454443512574910026390206427028816508564) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 294 = 60 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 15 +
      155 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_293_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_293_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_294_prefix_zero :
    (∑ x ∈ Finset.range 61,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (294 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (294 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_294_suffix_zero :
    (∑ x ∈ Finset.range 156,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (294 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_294 :
    recurrence2Scalar4Main.coeff 294 =
      -(((8326844638209811511101279525487177680189975815016685 * 10 ^ 70 +
        9439750374985942447245340364562126820725280381066470750621182230340205) * 10 ^ 70 +
        1671742946560392441723483904960099266175600183611830236267603656842758) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 295 = 61 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 14 +
      156 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_294_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_294_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_295_prefix_zero :
    (∑ x ∈ Finset.range 62,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (295 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (295 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_295_suffix_zero :
    (∑ x ∈ Finset.range 157,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (295 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_295 :
    recurrence2Scalar4Main.coeff 295 =
      (((1655974861162621423240881652975947595949156724525555 * 10 ^ 70 +
        0447252116993768879149247209889044467719241153521292196658093085123892) * 10 ^ 70 +
        5889179130660148444316382575652599672825243594189186299395447511875753) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 296 = 62 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 13 +
      157 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_295_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_295_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_296_prefix_zero :
    (∑ x ∈ Finset.range 63,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (296 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (296 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_296_suffix_zero :
    (∑ x ∈ Finset.range 158,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (296 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_296 :
    recurrence2Scalar4Main.coeff 296 =
      -(((287282305338686027914571939417532085380304755676750 * 10 ^ 70 +
        0391416903897825019836453835931715336745630632802189255541109941646310) * 10 ^ 70 +
        4662087760299934420843625717391533682920757232900060560328120769584215) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 297 = 63 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 12 +
      158 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_296_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_296_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_297_prefix_zero :
    (∑ x ∈ Finset.range 64,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (297 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (297 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_297_suffix_zero :
    (∑ x ∈ Finset.range 159,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (297 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_297 :
    recurrence2Scalar4Main.coeff 297 =
      (((41353634538388646484168953775309327911932753157465 * 10 ^ 70 +
        6768017534665343513880172563974553695758934059851116922376802386623845) * 10 ^ 70 +
        4857524707375061549368637572206401572230077117849303489070943896142531) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 298 = 64 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 11 +
      159 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_297_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_297_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_298_prefix_zero :
    (∑ x ∈ Finset.range 65,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (298 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (298 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_298_suffix_zero :
    (∑ x ∈ Finset.range 160,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (298 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_298 :
    recurrence2Scalar4Main.coeff 298 =
      -(((4178386597069775943276381818568407501631973892778 * 10 ^ 70 +
        0871016405058339894084043169912028382871828185330322079167068754066705) * 10 ^ 70 +
        4393371512530609575750703223781176525642711449913508577720870920967059) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 299 = 65 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 10 +
      160 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_298_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_298_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_299_prefix_zero :
    (∑ x ∈ Finset.range 66,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (299 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (299 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_299_suffix_zero :
    (∑ x ∈ Finset.range 161,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (299 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_299 :
    recurrence2Scalar4Main.coeff 299 =
      (((5495389629105047772323408871684288551250643382 * 10 ^ 70 +
        4990912986816103803140009333474642819237331465556376674930869766112279) * 10 ^ 70 +
        8059523084146845173990818411456109494185380348918953372039236095889736) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 300 = 66 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 9 +
      161 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_299_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_299_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_300_prefix_zero :
    (∑ x ∈ Finset.range 67,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (300 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (300 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_300_suffix_zero :
    (∑ x ∈ Finset.range 162,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (300 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_300 :
    recurrence2Scalar4Main.coeff 300 =
      (((135420193040473014640316302527284977584582788920 * 10 ^ 70 +
        8487383494818866674684507660814388664057791564954015270901230210055264) * 10 ^ 70 +
        4205484773822614885650738410985816383779927873843131024493947964518249) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 301 = 67 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 8 +
      162 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_300_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_300_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_301_prefix_zero :
    (∑ x ∈ Finset.range 68,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (301 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (301 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_301_suffix_zero :
    (∑ x ∈ Finset.range 163,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (301 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_301 :
    recurrence2Scalar4Main.coeff 301 =
      -(((44104912937880438306714102322609069539732957015 * 10 ^ 70 +
        9789224438193278484985191058122930521241913116947305435619471671472153) * 10 ^ 70 +
        6192828427194851855331182625183348932967085702249845737496178306071310) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 302 = 68 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 7 +
      163 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_301_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_301_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_302_prefix_zero :
    (∑ x ∈ Finset.range 69,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (302 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (302 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_302_suffix_zero :
    (∑ x ∈ Finset.range 164,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (302 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_302 :
    recurrence2Scalar4Main.coeff 302 =
      (((9911030065687357883971880177994653410723978869 * 10 ^ 70 +
        1495051721109084210031271803826925776527891845508593831592329633967587) * 10 ^ 70 +
        8970904228575958916249417772356085650247504127408416411492468342864358) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 303 = 69 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 6 +
      164 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_302_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_302_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_303_prefix_zero :
    (∑ x ∈ Finset.range 70,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (303 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (303 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_303_suffix_zero :
    (∑ x ∈ Finset.range 165,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (303 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_303 :
    recurrence2Scalar4Main.coeff 303 =
      -(((1807837875328883515311356953975232434470126860 * 10 ^ 70 +
        5975855266729791020101409256444092534458428335201604618282977623071387) * 10 ^ 70 +
        7821883642888077850739329375583938567642018414438244109294451151265061) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 304 = 70 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 5 +
      165 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_303_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_303_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_304_prefix_zero :
    (∑ x ∈ Finset.range 71,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (304 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (304 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_304_suffix_zero :
    (∑ x ∈ Finset.range 166,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (304 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_304 :
    recurrence2Scalar4Main.coeff 304 =
      (((278214221259425469815073353466747306421401896 * 10 ^ 70 +
        1474044529714025445239379133550683751540696628725977650597189419420379) * 10 ^ 70 +
        1005848501967200646628968781241451759677634455775010612747049945610492) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 305 = 71 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 4 +
      166 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_304_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_304_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_305_prefix_zero :
    (∑ x ∈ Finset.range 72,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (305 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (305 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_305_suffix_zero :
    (∑ x ∈ Finset.range 167,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (305 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_305 :
    recurrence2Scalar4Main.coeff 305 =
      -(((36001291726442072894691218386979893021623602 * 10 ^ 70 +
        2826499385966644845554732557004032103698199550909676243742757068642593) * 10 ^ 70 +
        7251464760094997118420009156393378963966775100457827500847276361900690) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 306 = 72 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 3 +
      167 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_305_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_305_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_306_prefix_zero :
    (∑ x ∈ Finset.range 73,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (306 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (306 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_306_suffix_zero :
    (∑ x ∈ Finset.range 168,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (306 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_306 :
    recurrence2Scalar4Main.coeff 306 =
      (((3738249621153094215332570364326009318342917 * 10 ^ 70 +
        0238407045485530254850719950465770606615890170069388003816817394042547) * 10 ^ 70 +
        3198080371735786997526230605878210347864328235513146382052538186881950) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 307 = 73 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 2 +
      168 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_306_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_306_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_307_prefix_zero :
    (∑ x ∈ Finset.range 74,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (307 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (307 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_307_suffix_zero :
    (∑ x ∈ Finset.range 169,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (307 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_307 :
    recurrence2Scalar4Main.coeff 307 =
      -(((259623903704500990260405745019338847096926 * 10 ^ 70 +
        6968346729949074218682280952890458905741824704820655523469827980502074) * 10 ^ 70 +
        7580866679276438736099906117810932651247780956368609651055466704847163) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 308 = 74 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 1 +
      169 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_307_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_307_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_308_prefix_zero :
    (∑ x ∈ Finset.range 75,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (308 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (308 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_308_suffix_zero :
    (∑ x ∈ Finset.range 170,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (308 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_308 :
    recurrence2Scalar4Main.coeff 308 =
      -(((2132849371403927486171425369690421626401 * 10 ^ 70 +
        8658958697265158244118438657351151258313158588906407742546131441526602) * 10 ^ 70 +
        4237372731828779065928499942993326796778427790213618323657636581190165) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 309 = 75 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_308_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_308_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_309_prefix_zero :
    (∑ x ∈ Finset.range 76,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (309 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (309 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_309_suffix_zero :
    (∑ x ∈ Finset.range 171,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (309 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_309 :
    recurrence2Scalar4Main.coeff 309 =
      (((4511209689888116567068573121491980303847 * 10 ^ 70 +
        1842625477204828575710598620328085541743100675189858196176485109616453) * 10 ^ 70 +
        5206124459645712669996392154827478692823375662338773223585378952950105) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 310 = 76 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 31 +
      171 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_309_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_309_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_310_prefix_zero :
    (∑ x ∈ Finset.range 77,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (310 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (310 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_310_suffix_zero :
    (∑ x ∈ Finset.range 172,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (310 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_310 :
    recurrence2Scalar4Main.coeff 310 =
      -(((934451341988013385458478257880226777721 * 10 ^ 70 +
        1630035329982503793824302202823223959924948089558000019520207118137141) * 10 ^ 70 +
        9662337566416448525233401291875079586459393960138986775091176856141512) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 311 = 77 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 30 +
      172 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_310_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_310_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_311_prefix_zero :
    (∑ x ∈ Finset.range 78,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (311 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (311 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_311_suffix_zero :
    (∑ x ∈ Finset.range 173,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (311 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_311 :
    recurrence2Scalar4Main.coeff 311 =
      (((131533121507892038452257433473873566443 * 10 ^ 70 +
        0382638536200923565760520268913393670605585416157968953300075969516923) * 10 ^ 70 +
        1924086595341852200610297960163147068253633037594278029320081945244583) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 312 = 78 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 29 +
      173 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_311_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_311_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_312_prefix_zero :
    (∑ x ∈ Finset.range 79,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (312 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (312 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_312_suffix_zero :
    (∑ x ∈ Finset.range 174,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (312 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_312 :
    recurrence2Scalar4Main.coeff 312 =
      -(((14376442849084453212451581835818132249 * 10 ^ 70 +
        9573884114612448688902343543476140198494669681072934329138547214222236) * 10 ^ 70 +
        0746225930029043287698656006872895261909110843464624724451451025722672) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 313 = 79 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 28 +
      174 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_312_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_312_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_313_prefix_zero :
    (∑ x ∈ Finset.range 80,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (313 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (313 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_313_suffix_zero :
    (∑ x ∈ Finset.range 175,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (313 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_313 :
    recurrence2Scalar4Main.coeff 313 =
      (((1225733572854300844824537679597521087 * 10 ^ 70 +
        6423882738037005593640432356299570788145604159590671028356979877753057) * 10 ^ 70 +
        5452928774353253243522974226865294235583041602683223758255308811319143) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 314 = 80 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 27 +
      175 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_313_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_313_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_314_prefix_zero :
    (∑ x ∈ Finset.range 81,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (314 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (314 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_314_suffix_zero :
    (∑ x ∈ Finset.range 176,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (314 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_314 :
    recurrence2Scalar4Main.coeff 314 =
      -(((73743440804838786042689531738145346 * 10 ^ 70 +
        9806863091191908321598983972814180156545045353559272280304008084313935) * 10 ^ 70 +
        2126363561733096139087453761996330890942070733499471895570766993059695) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 315 = 81 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 26 +
      176 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_314_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_314_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_315_prefix_zero :
    (∑ x ∈ Finset.range 82,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (315 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (315 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_315_suffix_zero :
    (∑ x ∈ Finset.range 177,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (315 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_315 :
    recurrence2Scalar4Main.coeff 315 =
      (((1483746889143372936967617266352200 * 10 ^ 70 +
        7120837758961503670764608238485808044988569419157913388197779454627161) * 10 ^ 70 +
        0926845726792911042249487642057694516881206052834197323041533458224340) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 316 = 82 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 25 +
      177 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_315_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_315_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_316_prefix_zero :
    (∑ x ∈ Finset.range 83,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (316 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (316 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_316_suffix_zero :
    (∑ x ∈ Finset.range 178,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (316 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_316 :
    recurrence2Scalar4Main.coeff 316 =
      (((332582480285990071443916857406742 * 10 ^ 70 +
        1305593223409146085944651657621160644035263336269227776764694533914116) * 10 ^ 70 +
        7200483931009217934057778481577591881104865021563343301928125527424971) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 317 = 83 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 24 +
      178 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_316_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_316_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_317_prefix_zero :
    (∑ x ∈ Finset.range 84,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (317 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (317 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_317_suffix_zero :
    (∑ x ∈ Finset.range 179,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (317 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_317 :
    recurrence2Scalar4Main.coeff 317 =
      -(((56763981880593889772840269087117 * 10 ^ 70 +
        2179745440811610889416810001096638315443585638969011867797420040256379) * 10 ^ 70 +
        3810290249793109250318575723568956525818335284263143947096802932632254) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 318 = 84 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 23 +
      179 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_317_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_317_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_318_prefix_zero :
    (∑ x ∈ Finset.range 85,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (318 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (318 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_318_suffix_zero :
    (∑ x ∈ Finset.range 180,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (318 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_318 :
    recurrence2Scalar4Main.coeff 318 =
      (((5479833466758775103251105797054 * 10 ^ 70 +
        8675852005104105992973486516233355860780878404211642235087686388192630) * 10 ^ 70 +
        3452616986020674586663179501447636749468771853918854491889193249646894) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 319 = 85 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 22 +
      180 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_318_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_318_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_319_prefix_zero :
    (∑ x ∈ Finset.range 86,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (319 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (319 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_319_suffix_zero :
    (∑ x ∈ Finset.range 181,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (319 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_319 :
    recurrence2Scalar4Main.coeff 319 =
      -(((372239508368341082421047320315 * 10 ^ 70 +
        6985087570555715121665859279957128711913810767054561891877375031166736) * 10 ^ 70 +
        2041058607401666932481501460169126564325896391555650545601122677142128) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 320 = 86 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 21 +
      181 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_319_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_319_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_320_prefix_zero :
    (∑ x ∈ Finset.range 87,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (320 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (320 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_320_suffix_zero :
    (∑ x ∈ Finset.range 182,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (320 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_320 :
    recurrence2Scalar4Main.coeff 320 =
      (((16998012372980106747312856277 * 10 ^ 70 +
        1280201506235855929756482292454308484243418362924543280058912482401222) * 10 ^ 70 +
        6315657881828954242157746425863927522900264568298294902293752492853707) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 321 = 87 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 20 +
      182 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_320_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_320_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_321_prefix_zero :
    (∑ x ∈ Finset.range 88,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (321 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (321 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_321_suffix_zero :
    (∑ x ∈ Finset.range 183,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (321 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_321 :
    recurrence2Scalar4Main.coeff 321 =
      -(((288339807445863622270916613 * 10 ^ 70 +
        0499337841502962510109618454030376307085495535065345012768528987271995) * 10 ^ 70 +
        7002290528256837187585898887981748952978718643181823291910794542030761) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 322 = 88 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 19 +
      183 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_321_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_321_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_322_prefix_zero :
    (∑ x ∈ Finset.range 89,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (322 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (322 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_322_suffix_zero :
    (∑ x ∈ Finset.range 184,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (322 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_322 :
    recurrence2Scalar4Main.coeff 322 =
      -(((31120484906599823554928476 * 10 ^ 70 +
        1040518025787782052736833991013392152826777237575125218733511977394561) * 10 ^ 70 +
        9240621523842011236245033881419214404851774773894506405669148750933216) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 323 = 89 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 18 +
      184 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_322_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_322_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_323_prefix_zero :
    (∑ x ∈ Finset.range 90,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (323 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (323 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_323_suffix_zero :
    (∑ x ∈ Finset.range 185,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (323 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_323 :
    recurrence2Scalar4Main.coeff 323 =
      (((3591014601363149578121296 * 10 ^ 70 +
        8885533394896063317182648242281788896594947796159024687451635786195366) * 10 ^ 70 +
        2193867954339897215115631841294451208556785314367944299918503475805246) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 324 = 90 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 17 +
      185 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_323_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_323_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_324_prefix_zero :
    (∑ x ∈ Finset.range 91,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (324 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (324 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_324_suffix_zero :
    (∑ x ∈ Finset.range 186,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (324 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_324 :
    recurrence2Scalar4Main.coeff 324 =
      -(((207980069907160280677862 * 10 ^ 70 +
        4491986981157429276213093773451726206150125234273414714834335128519960) * 10 ^ 70 +
        2059443460258599735080854967322409783074539660488603279019467135908906) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 325 = 91 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 16 +
      186 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_324_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_324_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_325_prefix_zero :
    (∑ x ∈ Finset.range 92,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (325 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (325 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_325_suffix_zero :
    (∑ x ∈ Finset.range 187,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (325 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_325 :
    recurrence2Scalar4Main.coeff 325 =
      (((7317276666580844788248 * 10 ^ 70 +
        3004018637408640347404269414755324093577357902725434712804390283068843) * 10 ^ 70 +
        8598498251322792887645768632196873046284274516129464324429663285651151) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 326 = 92 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 15 +
      187 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_325_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_325_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_326_prefix_zero :
    (∑ x ∈ Finset.range 93,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (326 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (326 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_326_suffix_zero :
    (∑ x ∈ Finset.range 188,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (326 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_326 :
    recurrence2Scalar4Main.coeff 326 =
      -(((100123225870060930115 * 10 ^ 70 +
        5050939884059879197663912902062345361057442699106288220756343945673171) * 10 ^ 70 +
        1566933128866222282056072038487854926660315901477765279155561919543939) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 327 = 93 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 14 +
      188 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_326_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_326_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_327_prefix_zero :
    (∑ x ∈ Finset.range 94,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (327 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (327 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_327_suffix_zero :
    (∑ x ∈ Finset.range 189,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (327 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_327 :
    recurrence2Scalar4Main.coeff 327 =
      -(((5191791652409168130 * 10 ^ 70 +
        2180883407228683600931109265685825998696034104800112905798001609416721) * 10 ^ 70 +
        7719957409431918230811974734872921324652165580055823386191542065096194) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 328 = 94 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 13 +
      189 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_327_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_327_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_328_prefix_zero :
    (∑ x ∈ Finset.range 95,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (328 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (328 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_328_suffix_zero :
    (∑ x ∈ Finset.range 190,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (328 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_328 :
    recurrence2Scalar4Main.coeff 328 =
      (((391866672532194793 * 10 ^ 70 +
        7556468485905934245370055782840244645980634279037995869776569569688426) * 10 ^ 70 +
        3436204549441663619113975758897244148620978765673419011151285475943856) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 329 = 95 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 12 +
      190 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_328_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_328_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_329_prefix_zero :
    (∑ x ∈ Finset.range 96,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (329 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (329 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_329_suffix_zero :
    (∑ x ∈ Finset.range 191,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (329 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_329 :
    recurrence2Scalar4Main.coeff 329 =
      -(((12518275346454514 * 10 ^ 70 +
        0362261082901951208530493912028486927208497717046878516798496289858049) * 10 ^ 70 +
        0455130661152440681343425732706267719532901491465687548953313078628252) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 330 = 96 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 11 +
      191 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_329_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_329_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_330_prefix_zero :
    (∑ x ∈ Finset.range 97,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (330 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (330 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_330_suffix_zero :
    (∑ x ∈ Finset.range 192,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (330 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_330 :
    recurrence2Scalar4Main.coeff 330 =
      (((175448859240203 * 10 ^ 70 +
        4179616810758871379133974612794226713573391832830909254588169936788910) * 10 ^ 70 +
        3374997037546132336216271194745666339016193387127838854291173429695276) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 331 = 97 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 10 +
      192 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_330_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_330_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_331_prefix_zero :
    (∑ x ∈ Finset.range 98,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (331 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (331 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_331_suffix_zero :
    (∑ x ∈ Finset.range 193,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (331 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_331 :
    recurrence2Scalar4Main.coeff 331 =
      (((2118942344532 * 10 ^ 70 +
        4086505362712396858149762652755725608262119058375143947217167804698002) * 10 ^ 70 +
        4988857708969314686301494481715154910627760197733587113556916011643586) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 332 = 98 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 9 +
      193 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_331_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_331_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_332_prefix_zero :
    (∑ x ∈ Finset.range 99,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (332 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (332 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_332_suffix_zero :
    (∑ x ∈ Finset.range 194,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (332 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_332 :
    recurrence2Scalar4Main.coeff 332 =
      -(((149674259055 * 10 ^ 70 +
        6837132372323569187050579323740934512328060461047704849127805719009650) * 10 ^ 70 +
        9212275501921088501564904554870624486082303355067150669952451969861863) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 333 = 99 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 8 +
      194 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_332_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_332_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_333_prefix_zero :
    (∑ x ∈ Finset.range 100,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (333 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (333 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_333_suffix_zero :
    (∑ x ∈ Finset.range 195,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (333 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_333 :
    recurrence2Scalar4Main.coeff 333 =
      (((2778826780 * 10 ^ 70 +
        8269975314009219716930860566730614241076851812372285401559927465493407) * 10 ^ 70 +
        8053045607798327698482664895390519443736466196366189273822378089124033) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 334 = 100 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 7 +
      195 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_333_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_333_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_334_prefix_zero :
    (∑ x ∈ Finset.range 101,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (334 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (334 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_334_suffix_zero :
    (∑ x ∈ Finset.range 196,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (334 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_334 :
    recurrence2Scalar4Main.coeff 334 =
      -(((10317356 * 10 ^ 70 +
        0220693548602020449969876738804150316334169010859477984848027335900875) * 10 ^ 70 +
        0825829699815110115548197092020113538943571447904807467640323466853824) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 335 = 101 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 6 +
      196 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_334_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_334_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_335_prefix_zero :
    (∑ x ∈ Finset.range 102,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (335 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (335 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_335_suffix_zero :
    (∑ x ∈ Finset.range 197,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (335 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_335 :
    recurrence2Scalar4Main.coeff 335 =
      -(((466168 * 10 ^ 70 +
        0592020954071259713624506023697179700968393337018327460125314315627783) * 10 ^ 70 +
        3460374679281993814635908192608991518647106409794891839964022785445562) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 336 = 102 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 5 +
      197 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_335_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_335_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_336_prefix_zero :
    (∑ x ∈ Finset.range 103,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (336 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (336 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_336_suffix_zero :
    (∑ x ∈ Finset.range 198,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (336 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_336 :
    recurrence2Scalar4Main.coeff 336 =
      (((7672 * 10 ^ 70 +
        8218894079877629693416872468432592603237888947879514609923207578777790) * 10 ^ 70 +
        4494584904154253336647507836856894259269913000914854717344473882153104) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 337 = 103 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 4 +
      198 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_336_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_336_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_337_prefix_zero :
    (∑ x ∈ Finset.range 104,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (337 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (337 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_337_suffix_zero :
    (∑ x ∈ Finset.range 199,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (337 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_337 :
    recurrence2Scalar4Main.coeff 337 =
      -(((13 * 10 ^ 70 +
        9279436753550193310022080342645460520700739277217312106640716756102310) * 10 ^ 70 +
        6202001131364272250544137632032721118031177174215794930620854947317471) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 338 = 104 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 3 +
      199 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_337_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_337_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_338_prefix_zero :
    (∑ x ∈ Finset.range 105,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (338 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (338 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_338_suffix_zero :
    (∑ x ∈ Finset.range 200,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (338 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_338 :
    recurrence2Scalar4Main.coeff 338 =
      -((6768901112796948330797364816067754188532295582035801020535642476213945 * 10 ^ 70 +
        3463518671208485934256562951130370281985639053355478438782870494532804) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 339 = 105 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 2 +
      200 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_338_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_338_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_339_prefix_zero :
    (∑ x ∈ Finset.range 106,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (339 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (339 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_339_suffix_zero :
    (∑ x ∈ Finset.range 201,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (339 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_339 :
    recurrence2Scalar4Main.coeff 339 =
      ((50047998480221614142670129055170913048959860830186695623695658603553 * 10 ^ 70 +
        3008989383834671762717490855283444131258367942248017998957973967776277) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 340 = 106 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 1 +
      201 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_339_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_339_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_340_prefix_zero :
    (∑ x ∈ Finset.range 107,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (340 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (340 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_340_suffix_zero :
    (∑ x ∈ Finset.range 202,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (340 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_340 :
    recurrence2Scalar4Main.coeff 340 =
      ((203238382400772743897243569845242412211683060419604913152000153464 * 10 ^ 70 +
        0747564446412864056635367728822597939645119075268417412471991558468102) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 341 = 107 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_340_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_340_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_341_prefix_zero :
    (∑ x ∈ Finset.range 108,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (341 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (341 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_341_suffix_zero :
    (∑ x ∈ Finset.range 203,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (341 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_341 :
    recurrence2Scalar4Main.coeff 341 =
      -((3161818840757676793503188423627757447001853830161005964664242692 * 10 ^ 70 +
        4988100134336171079492513402165815892672471738776132086575902242560244) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 342 = 108 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 31 +
      203 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_341_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_341_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_342_prefix_zero :
    (∑ x ∈ Finset.range 109,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (342 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (342 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_342_suffix_zero :
    (∑ x ∈ Finset.range 204,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (342 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_342 :
    recurrence2Scalar4Main.coeff 342 =
      ((608641907750130987679017566128061465169305005824196896453586 * 10 ^ 70 +
        1369633015939684980643063807154494206457580667730875773897909803580076) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 343 = 109 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 30 +
      204 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_342_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_342_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_343_prefix_zero :
    (∑ x ∈ Finset.range 110,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (343 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (343 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_343_suffix_zero :
    (∑ x ∈ Finset.range 205,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (343 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_343 :
    recurrence2Scalar4Main.coeff 343 =
      ((95174457914842574603775525304973426082444829424988714861235 * 10 ^ 70 +
        7868791639805772105873029451879385561995216403925366543817779985529031) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 344 = 110 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 29 +
      205 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_343_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_343_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_344_prefix_zero :
    (∑ x ∈ Finset.range 111,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (344 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (344 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_344_suffix_zero :
    (∑ x ∈ Finset.range 206,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (344 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_344 :
    recurrence2Scalar4Main.coeff 344 =
      -((187644952346744226541368696809696355057616735442224697855 * 10 ^ 70 +
        0182796013902788653070944896191259663269717981431486848587137595367218) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 345 = 111 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 28 +
      206 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_344_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_344_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_345_prefix_zero :
    (∑ x ∈ Finset.range 112,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (345 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (345 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_345_suffix_zero :
    (∑ x ∈ Finset.range 207,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (345 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_345 :
    recurrence2Scalar4Main.coeff 345 =
      -((1501728935330941176331480042132382471071653744855757928 * 10 ^ 70 +
        1063635831527891055082783630517633016674478752042495247253591014655046) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 346 = 112 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 27 +
      207 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_345_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_345_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_346_prefix_zero :
    (∑ x ∈ Finset.range 113,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (346 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (346 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_346_suffix_zero :
    (∑ x ∈ Finset.range 208,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (346 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_346 :
    recurrence2Scalar4Main.coeff 346 =
      ((4978473138228283607848265821256543165102011323715498 * 10 ^ 70 +
        3532763147724641073706692085020083274389212168531233070020573451153762) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 347 = 113 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 26 +
      208 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_346_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_346_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_347_prefix_zero :
    (∑ x ∈ Finset.range 114,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (347 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (347 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_347_suffix_zero :
    (∑ x ∈ Finset.range 209,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (347 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_347 :
    recurrence2Scalar4Main.coeff 347 =
      ((10782825954559814152491654222237200769510731561315 * 10 ^ 70 +
        3074961544216308119625323122573706059570416259568304419464522097845031) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 348 = 114 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 25 +
      209 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_347_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_347_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_348_prefix_zero :
    (∑ x ∈ Finset.range 115,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (348 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (348 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_348_suffix_zero :
    (∑ x ∈ Finset.range 210,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (348 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_348 :
    recurrence2Scalar4Main.coeff 348 =
      -((60484886024567935011333062453894764355837110242 * 10 ^ 70 +
        1281944126283898995771553853480706224833416397510387981566631979069603) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 349 = 115 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 24 +
      210 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_348_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_348_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_349_prefix_zero :
    (∑ x ∈ Finset.range 116,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (349 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (349 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_349_suffix_zero :
    (∑ x ∈ Finset.range 211,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (349 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_349 :
    recurrence2Scalar4Main.coeff 349 =
      ((2239761998168885905795736546945522933019215 * 10 ^ 70 +
        9425849089505732770561719368181963757429868549681064870440899411525664) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 350 = 116 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 23 +
      211 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_349_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_349_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_350_prefix_zero :
    (∑ x ∈ Finset.range 117,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (350 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (350 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_350_suffix_zero :
    (∑ x ∈ Finset.range 212,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (350 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_350 :
    recurrence2Scalar4Main.coeff 350 =
      ((338008142964102138783900097877450502615595 * 10 ^ 70 +
        9036882433461452293682954520803773661261083957710232864064157103693454) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 351 = 117 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 22 +
      212 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_350_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_350_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_351_prefix_zero :
    (∑ x ∈ Finset.range 118,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (351 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (351 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_351_suffix_zero :
    (∑ x ∈ Finset.range 213,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (351 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_351 :
    recurrence2Scalar4Main.coeff 351 =
      -((460184617602511168694197846339400879945 * 10 ^ 70 +
        9659641614347398656285451358836356205686076860419058845060605382703361) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 352 = 118 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 21 +
      213 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_351_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_351_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_352_prefix_zero :
    (∑ x ∈ Finset.range 119,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (352 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (352 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_352_suffix_zero :
    (∑ x ∈ Finset.range 214,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (352 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_352 :
    recurrence2Scalar4Main.coeff 352 =
      -((486854329370610717393301034315004317 * 10 ^ 70 +
        9472197179508159351327156926431611401194423563101334452012770787045702) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 353 = 119 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 20 +
      214 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_352_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_352_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_353_prefix_zero :
    (∑ x ∈ Finset.range 120,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (353 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (353 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_353_suffix_zero :
    (∑ x ∈ Finset.range 215,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (353 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_353 :
    recurrence2Scalar4Main.coeff 353 =
      ((1732227423464865457183261658892127 * 10 ^ 70 +
        0940259075485114255254075349954703798842411914377244017959111212815079) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 354 = 120 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 19 +
      215 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_353_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_353_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_354_prefix_zero :
    (∑ x ∈ Finset.range 121,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (354 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (354 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_354_suffix_zero :
    (∑ x ∈ Finset.range 216,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (354 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_354 :
    recurrence2Scalar4Main.coeff 354 =
      -((1429458550822710305424495862725 * 10 ^ 70 +
        8107677116858646672045485930020969755578052475563289170490236255830730) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 355 = 121 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 18 +
      216 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_354_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_354_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_355_prefix_zero :
    (∑ x ∈ Finset.range 122,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (355 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (355 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_355_suffix_zero :
    (∑ x ∈ Finset.range 217,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (355 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_355 :
    recurrence2Scalar4Main.coeff 355 =
      -((38562479733890366927029680 * 10 ^ 70 +
        1474873125368188037379622476358145628046575847395778584123031904457894) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 356 = 122 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 17 +
      217 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_355_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_355_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_356_prefix_zero :
    (∑ x ∈ Finset.range 123,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (356 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (356 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_356_suffix_zero :
    (∑ x ∈ Finset.range 218,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (356 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_356 :
    recurrence2Scalar4Main.coeff 356 =
      ((734047538805810172717340 * 10 ^ 70 +
        5540368490600061551311631819586188274563785874661426940061201719702669) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 357 = 123 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 16 +
      218 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_356_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_356_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_357_prefix_zero :
    (∑ x ∈ Finset.range 124,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (357 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (357 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_357_suffix_zero :
    (∑ x ∈ Finset.range 219,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (357 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_357 :
    recurrence2Scalar4Main.coeff 357 =
      -((438639267058510527736 * 10 ^ 70 +
        1702399951526991322180180772658904217557268924622096558071761118395124) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 358 = 124 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 15 +
      219 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_357_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_357_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_358_prefix_zero :
    (∑ x ∈ Finset.range 125,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (358 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (358 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_358_suffix_zero :
    (∑ x ∈ Finset.range 220,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (358 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_358 :
    recurrence2Scalar4Main.coeff 358 =
      ((99227501656948566 * 10 ^ 70 +
        1737315898521566094474859737354080885511086537264534434612901512215316) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 359 = 125 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 14 +
      220 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_358_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_358_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_359_prefix_zero :
    (∑ x ∈ Finset.range 126,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (359 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (359 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_359_suffix_zero :
    (∑ x ∈ Finset.range 221,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (359 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_359 :
    recurrence2Scalar4Main.coeff 359 =
      -((4747341365349 * 10 ^ 70 +
        5520043144077886441733598688614420192205479046223753563237582053500941) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 360 = 126 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 13 +
      221 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_359_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_359_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_360_prefix_zero :
    (∑ x ∈ Finset.range 127,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (360 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (360 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_360_suffix_zero :
    (∑ x ∈ Finset.range 222,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (360 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_360 :
    recurrence2Scalar4Main.coeff 360 =
      -((1316674573 * 10 ^ 70 +
        9665998426507440038218392018956230804629969401873793898302148231621339) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 361 = 127 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 12 +
      222 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_360_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_360_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_361_prefix_zero :
    (∑ x ∈ Finset.range 128,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (361 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (361 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_361_suffix_zero :
    (∑ x ∈ Finset.range 223,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (361 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_361 :
    recurrence2Scalar4Main.coeff 361 =
      ((185250 * 10 ^ 70 +
        4049915846592588213863773271466526337372713361270009496420176218542802) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 362 = 128 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 11 +
      223 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_361_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_361_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_362_prefix_zero :
    (∑ x ∈ Finset.range 129,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (362 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (362 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_362_suffix_zero :
    (∑ x ∈ Finset.range 224,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (362 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_362 :
    recurrence2Scalar4Main.coeff 362 =
      -((7 * 10 ^ 70 +
        8319477727698935084646778029265032085700797311552944892273117685568066) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 363 = 129 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 10 +
      224 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_362_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_362_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_363_prefix_zero :
    (∑ x ∈ Finset.range 130,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (363 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (363 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_363_suffix_zero :
    (∑ x ∈ Finset.range 225,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (363 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_363 :
    recurrence2Scalar4Main.coeff 363 =
      (1072590899515031018907349360100202923947214905133029305224169940628 : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 364 = 130 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 9 +
      225 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_363_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_363_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_364_prefix_zero :
    (∑ x ∈ Finset.range 131,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (364 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (364 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_364_suffix_zero :
    (∑ x ∈ Finset.range 226,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (364 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_364 :
    recurrence2Scalar4Main.coeff 364 =
      (792142129488169604722547024201125960536183086058333661577722 : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 365 = 131 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 8 +
      226 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_364_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_364_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_365_prefix_zero :
    (∑ x ∈ Finset.range 132,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (365 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (365 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_365_suffix_zero :
    (∑ x ∈ Finset.range 227,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (365 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_365 :
    recurrence2Scalar4Main.coeff 365 =
      (-59479285883399135928086547514117232773062183002721438917 : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 366 = 132 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 7 +
      227 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_365_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_365_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_366_prefix_zero :
    (∑ x ∈ Finset.range 133,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (366 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (366 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_366_suffix_zero :
    (∑ x ∈ Finset.range 228,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (366 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_366 :
    recurrence2Scalar4Main.coeff 366 =
      (202120554071303608419766685783396308385373365315958 : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 367 = 133 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 6 +
      228 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_366_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_366_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_367_prefix_zero :
    (∑ x ∈ Finset.range 134,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (367 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (367 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_367_suffix_zero :
    (∑ x ∈ Finset.range 229,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (367 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_367 :
    recurrence2Scalar4Main.coeff 367 =
      (-118239830108327367970173248835837267573366070 : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 368 = 134 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 5 +
      229 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_367_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_367_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_368_prefix_zero :
    (∑ x ∈ Finset.range 135,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (368 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (368 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_368_suffix_zero :
    (∑ x ∈ Finset.range 230,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (368 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_368 :
    recurrence2Scalar4Main.coeff 368 =
      (16947566945305068876048021264578210060 : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 369 = 135 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 4 +
      230 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_368_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_368_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_369_prefix_zero :
    (∑ x ∈ Finset.range 136,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (369 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (369 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_369_suffix_zero :
    (∑ x ∈ Finset.range 231,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (369 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_369 :
    recurrence2Scalar4Main.coeff 369 =
      (111104464423783079712050603284 : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 370 = 136 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 3 +
      231 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_369_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_369_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_370_prefix_zero :
    (∑ x ∈ Finset.range 137,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (370 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (370 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_370_suffix_zero :
    (∑ x ∈ Finset.range 232,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (370 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_370 :
    recurrence2Scalar4Main.coeff 370 =
      (-672793960729382441168 : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 371 = 137 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 2 +
      232 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_370_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_370_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_371_prefix_zero :
    (∑ x ∈ Finset.range 138,
      remainder3Coefficient4.coeff x * recurrence2QuotientConstant.coeff (371 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (371 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Main_coeff_371_suffix_zero :
    (∑ x ∈ Finset.range 233,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (371 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_371 :
    recurrence2Scalar4Main.coeff 371 =
      (631370089744 : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 372 = 138 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 1 +
      233 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Main_coeff_371_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_371_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
