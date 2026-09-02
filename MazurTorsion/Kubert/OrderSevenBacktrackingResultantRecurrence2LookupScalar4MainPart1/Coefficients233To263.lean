/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB4
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupQuotientConstant
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar4MainPart1Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: Scalar4Main coefficient convolution

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/
public section
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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
