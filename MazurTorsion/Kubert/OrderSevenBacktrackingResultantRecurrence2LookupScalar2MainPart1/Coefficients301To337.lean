/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB2
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupQuotientConstant
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar2MainPart1Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: Scalar2Main coefficient convolution

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence2B2_coeff_0
  recurrence2B2_coeff_1
  recurrence2B2_coeff_2
  recurrence2B2_coeff_3
  recurrence2B2_coeff_4
  recurrence2B2_coeff_5
  recurrence2B2_coeff_6
  recurrence2B2_coeff_7
  recurrence2B2_coeff_8
  recurrence2B2_coeff_9
  recurrence2B2_coeff_10
  recurrence2B2_coeff_11
  recurrence2B2_coeff_12
  recurrence2B2_coeff_13
  recurrence2B2_coeff_14
  recurrence2B2_coeff_15
  recurrence2B2_coeff_16
  recurrence2B2_coeff_17
  recurrence2B2_coeff_18
  recurrence2B2_coeff_19
  recurrence2B2_coeff_20
  recurrence2B2_coeff_21
  recurrence2B2_coeff_22
  recurrence2B2_coeff_23
  recurrence2B2_coeff_24
  recurrence2B2_coeff_25
  recurrence2B2_coeff_26
  recurrence2B2_coeff_27
  recurrence2B2_coeff_28
  recurrence2B2_coeff_29
  recurrence2B2_coeff_30
  recurrence2B2_coeff_31
  recurrence2B2_coeff_32
  recurrence2B2_coeff_33
  recurrence2B2_coeff_34
  recurrence2B2_coeff_35
  recurrence2B2_coeff_36
  recurrence2B2_coeff_37
  recurrence2B2_coeff_38
  recurrence2B2_coeff_39
  recurrence2B2_coeff_40
  recurrence2B2_coeff_41
  recurrence2B2_coeff_42
  recurrence2B2_coeff_43
  recurrence2B2_coeff_44
  recurrence2B2_coeff_45
  recurrence2B2_coeff_46
  recurrence2B2_coeff_47
  recurrence2B2_coeff_48
  recurrence2B2_coeff_49
  recurrence2B2_coeff_50
  recurrence2B2_coeff_51
  recurrence2B2_coeff_52
  recurrence2B2_coeff_53
  recurrence2B2_coeff_54
  recurrence2B2_coeff_55
  recurrence2B2_coeff_56
  recurrence2B2_coeff_57
  recurrence2B2_coeff_58
  recurrence2B2_coeff_59
  recurrence2B2_coeff_60
  recurrence2B2_coeff_61
  recurrence2B2_coeff_62
  recurrence2B2_coeff_63
  recurrence2B2_coeff_64
  recurrence2B2_coeff_65
  recurrence2B2_coeff_66
  recurrence2B2_coeff_67
  recurrence2B2_coeff_68
  recurrence2B2_coeff_69
  recurrence2B2_coeff_70
  recurrence2B2_coeff_71
  recurrence2B2_coeff_72
  recurrence2B2_coeff_73
  recurrence2B2_coeff_74
  recurrence2B2_coeff_75
  recurrence2B2_coeff_76
  recurrence2B2_coeff_77
  recurrence2B2_coeff_78
  recurrence2B2_coeff_79
  recurrence2B2_coeff_80
  recurrence2B2_coeff_81
  recurrence2B2_coeff_82
  recurrence2B2_coeff_83
  recurrence2B2_coeff_84
  recurrence2B2_coeff_85
  recurrence2B2_coeff_86
  recurrence2B2_coeff_87
  recurrence2B2_coeff_88
  recurrence2B2_coeff_89
  recurrence2B2_coeff_90
  recurrence2B2_coeff_91
  recurrence2B2_coeff_92
  recurrence2B2_coeff_93
  recurrence2B2_coeff_94
  recurrence2B2_coeff_95
  recurrence2B2_coeff_96
  recurrence2B2_coeff_97
  recurrence2B2_coeff_98
  recurrence2B2_coeff_99
  recurrence2B2_coeff_100
  recurrence2B2_coeff_101
  recurrence2B2_coeff_102
  recurrence2B2_coeff_103
  recurrence2B2_coeff_104
  recurrence2B2_coeff_105
  recurrence2B2_coeff_106
  recurrence2B2_coeff_107
  recurrence2B2_coeff_108
  recurrence2B2_coeff_109
  recurrence2B2_coeff_110
  recurrence2B2_coeff_111
  recurrence2B2_coeff_112
  recurrence2B2_coeff_113
  recurrence2B2_coeff_114
  recurrence2B2_coeff_115
  recurrence2B2_coeff_116
  recurrence2B2_coeff_117
  recurrence2B2_coeff_118
  recurrence2B2_coeff_119
  recurrence2B2_coeff_120
  recurrence2B2_coeff_121
  recurrence2B2_coeff_122
  recurrence2B2_coeff_123
  recurrence2B2_coeff_124
  recurrence2B2_coeff_125
  recurrence2B2_coeff_126
  recurrence2B2_coeff_127
  recurrence2B2_coeff_128
  recurrence2B2_coeff_129
  recurrence2B2_coeff_130
  recurrence2B2_coeff_131
  recurrence2B2_coeff_132
  recurrence2B2_coeff_133
  recurrence2B2_coeff_134
  recurrence2B2_coeff_135
  recurrence2B2_coeff_136
  recurrence2B2_coeff_137
  recurrence2B2_coeff_138
  recurrence2B2_coeff_139
  recurrence2B2_coeff_140
  recurrence2B2_coeff_141
  recurrence2B2_coeff_142
  recurrence2B2_coeff_143
  recurrence2B2_coeff_144
  recurrence2B2_coeff_145
  recurrence2B2_coeff_146
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

private theorem recurrence2Scalar2Main_coeff_301_prefix_zero :
    (∑ x ∈ Finset.range 68,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (301 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (301 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_301_suffix_zero :
    (∑ x ∈ Finset.range 155,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (301 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_301 :
    recurrence2Scalar2Main.coeff 301 =
      -(((21170464373738621892723282400915707765604654725164029 * 10 ^ 70 +
        2005354607375025425456917305518630485240482709692101557585360032489103) * 10 ^ 70 +
        4702688822338671606791305001056985051113400284071334708839983236289638) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 170 = 15 +
      155 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_301_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_301_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Main_coeff_302_prefix_zero :
    (∑ x ∈ Finset.range 69,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (302 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (302 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_302_suffix_zero :
    (∑ x ∈ Finset.range 156,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (302 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_302 :
    recurrence2Scalar2Main.coeff 302 =
      (((2818335266513672689544564166152887145049835559013146 * 10 ^ 70 +
        8851955079167670353410343981724639008009727751827563472554543562439305) * 10 ^ 70 +
        1706840579806917838185816404055225571502274725558103928006059568010926) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 170 = 14 +
      156 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_302_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_302_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Main_coeff_303_prefix_zero :
    (∑ x ∈ Finset.range 70,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (303 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (303 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_303_suffix_zero :
    (∑ x ∈ Finset.range 157,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (303 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_303 :
    recurrence2Scalar2Main.coeff 303 =
      -(((215211361399415567351107272315201589794950755209094 * 10 ^ 70 +
        5468231022731365246238259831858174014361189181265772854079073273678389) * 10 ^ 70 +
        7285878249979574234362483347417020387843812891813938018922962558350954) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 170 = 13 +
      157 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_303_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_303_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Main_coeff_304_prefix_zero :
    (∑ x ∈ Finset.range 71,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (304 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (304 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_304_suffix_zero :
    (∑ x ∈ Finset.range 158,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (304 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_304 :
    recurrence2Scalar2Main.coeff 304 =
      -(((25655088010431365572279143252609254877993547523339 * 10 ^ 70 +
        4991214762932108103032254120192317444069406465036455732049901020945573) * 10 ^ 70 +
        0400648382987599903447669309751784866098411133861976379550508652164103) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 170 = 12 +
      158 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_304_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_304_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Main_coeff_305_prefix_zero :
    (∑ x ∈ Finset.range 72,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (305 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (305 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_305_suffix_zero :
    (∑ x ∈ Finset.range 159,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (305 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_305 :
    recurrence2Scalar2Main.coeff 305 =
      (((15928205103947592158422555561978224296959340630963 * 10 ^ 70 +
        7627673275098542902887748802610820397293858007146128938800934595181507) * 10 ^ 70 +
        2708240677275150731636783017645421963308277289821177729452356014142166) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 170 = 11 +
      159 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_305_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_305_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Main_coeff_306_prefix_zero :
    (∑ x ∈ Finset.range 73,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (306 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (306 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_306_suffix_zero :
    (∑ x ∈ Finset.range 160,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (306 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_306 :
    recurrence2Scalar2Main.coeff 306 =
      -(((4386959081253642078921110532638695914016023872308 * 10 ^ 70 +
        0217753332414880242100993587655289596256044244120374823897694434253429) * 10 ^ 70 +
        5531971709012769387273348949705061796351704254456888681862653796668911) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 170 = 10 +
      160 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_306_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_306_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Main_coeff_307_prefix_zero :
    (∑ x ∈ Finset.range 74,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (307 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (307 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_307_suffix_zero :
    (∑ x ∈ Finset.range 161,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (307 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_307 :
    recurrence2Scalar2Main.coeff 307 =
      (((908386340541312841417722561243374984341361805048 * 10 ^ 70 +
        6997534597457597111477425646916549156792054022375932149369079949603527) * 10 ^ 70 +
        3431065356562711706644030046578271843926203922449257977122634309717070) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 170 = 9 +
      161 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_307_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_307_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Main_coeff_308_prefix_zero :
    (∑ x ∈ Finset.range 75,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (308 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (308 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_308_suffix_zero :
    (∑ x ∈ Finset.range 162,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (308 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_308 :
    recurrence2Scalar2Main.coeff 308 =
      -(((153727892576582970625211646249494666110700947070 * 10 ^ 70 +
        3157952867407460386507911986304199040171756788017394661227110249057387) * 10 ^ 70 +
        0483636170183262964824708151644094313627477382281470135241732373973273) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rhs
    rw [show 170 = 8 +
      162 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_308_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_308_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Main_coeff_309_prefix_zero :
    (∑ x ∈ Finset.range 76,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (309 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (309 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_309_suffix_zero :
    (∑ x ∈ Finset.range 163,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (309 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_309 :
    recurrence2Scalar2Main.coeff 309 =
      (((21329511856300208254493206760136018560227106608 * 10 ^ 70 +
        0730987901528999335091067310461525559611321201537574160405723832882486) * 10 ^ 70 +
        8451602782769578004067846330579687732620320466505618904751268241749227) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 7 +
      163 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_309_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_309_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Main_coeff_310_prefix_zero :
    (∑ x ∈ Finset.range 77,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (310 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (310 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_310_suffix_zero :
    (∑ x ∈ Finset.range 164,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (310 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_310 :
    recurrence2Scalar2Main.coeff 310 =
      -(((2273737809544632903579334343738194693119385637 * 10 ^ 70 +
        0258170183160269288938669151556383570319479619864942123363741459735350) * 10 ^ 70 +
        7941333621010097839434944111818590020695005990597597449091659672030240) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 6 +
      164 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_310_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_310_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Main_coeff_311_prefix_zero :
    (∑ x ∈ Finset.range 78,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (311 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (311 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_311_suffix_zero :
    (∑ x ∈ Finset.range 165,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (311 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_311 :
    recurrence2Scalar2Main.coeff 311 =
      (((134214532129183609346247028275748579473234880 * 10 ^ 70 +
        9024370769590953138088075606963309203360134921909464474168343701022030) * 10 ^ 70 +
        2162553730386723286667795181185887992749992034386646953055127790633408) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 5 +
      165 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_311_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_311_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Main_coeff_312_prefix_zero :
    (∑ x ∈ Finset.range 79,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (312 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (312 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_312_suffix_zero :
    (∑ x ∈ Finset.range 166,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (312 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_312 :
    recurrence2Scalar2Main.coeff 312 =
      (((12493424611427153331723093530042274950986344 * 10 ^ 70 +
        2725885380839457228711446693456085468073345574437023874542682530203666) * 10 ^ 70 +
        1915751790479403540664216535013896867132779670421623625448440027984032) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 4 +
      166 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_312_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_312_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Main_coeff_313_prefix_zero :
    (∑ x ∈ Finset.range 80,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (313 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (313 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_313_suffix_zero :
    (∑ x ∈ Finset.range 167,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (313 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_313 :
    recurrence2Scalar2Main.coeff 313 =
      -(((5623120651188670557216490603122332544579835 * 10 ^ 70 +
        5009011802452248627798316418850390195461864112543017447373758251070684) * 10 ^ 70 +
        5892977886891049393813272068943568446527707148331420432777078992408624) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 3 +
      167 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_313_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_313_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Main_coeff_314_prefix_zero :
    (∑ x ∈ Finset.range 81,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (314 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (314 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_314_suffix_zero :
    (∑ x ∈ Finset.range 168,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (314 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_314 :
    recurrence2Scalar2Main.coeff 314 =
      (((1094627725689114679939767731310066714665936 * 10 ^ 70 +
        8613430256961959816411554316216628310232233787158288573508804359368898) * 10 ^ 70 +
        6876170679520880940546423002959395085770768215571139520602774105655519) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 2 +
      168 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_314_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_314_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Main_coeff_315_prefix_zero :
    (∑ x ∈ Finset.range 82,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (315 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (315 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_315_suffix_zero :
    (∑ x ∈ Finset.range 169,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (315 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_315 :
    recurrence2Scalar2Main.coeff 315 =
      -(((152322329276388894703369238461401004621429 * 10 ^ 70 +
        2071727273759022031729247174845498340554286329096792651829175919794879) * 10 ^ 70 +
        2072902017167960799491923996379719192616435017194247746103673328365149) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 1 +
      169 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_315_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_315_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Main_coeff_316_prefix_zero :
    (∑ x ∈ Finset.range 83,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (316 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (316 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_316_suffix_zero :
    (∑ x ∈ Finset.range 170,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (316 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_316 :
    recurrence2Scalar2Main.coeff 316 =
      (((15819122470015665910992181377801554309292 * 10 ^ 70 +
        6879864347272926119564600229840575905641830316120438654097142405459297) * 10 ^ 70 +
        0602524327239836364990104917267582970435763648925864573508362915964892) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_316_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_316_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Main_coeff_317_prefix_zero :
    (∑ x ∈ Finset.range 84,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (317 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (317 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_317_suffix_zero :
    (∑ x ∈ Finset.range 171,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (317 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_317 :
    recurrence2Scalar2Main.coeff 317 =
      -(((1062186299827485473260143374495715951985 * 10 ^ 70 +
        8190507185592081405625976989047999636488739421269874205430186847035961) * 10 ^ 70 +
        7735853662510747333926469955350307212687431782032580374301082840224305) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 202 = 31 +
      171 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_317_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_317_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Main_coeff_318_prefix_zero :
    (∑ x ∈ Finset.range 85,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (318 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (318 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_318_suffix_zero :
    (∑ x ∈ Finset.range 172,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (318 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_318 :
    recurrence2Scalar2Main.coeff 318 =
      -(((3277274167399156481628990860054198686 * 10 ^ 70 +
        8399683847141329859111034426049221386923083304450282620486716418075408) * 10 ^ 70 +
        9270479854303926060135031995360199710292642127739598048935096308036830) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 202 = 30 +
      172 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_318_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_318_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Main_coeff_319_prefix_zero :
    (∑ x ∈ Finset.range 86,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (319 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (319 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_319_suffix_zero :
    (∑ x ∈ Finset.range 173,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (319 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_319 :
    recurrence2Scalar2Main.coeff 319 =
      (((14052810434814592773488023583126804356 * 10 ^ 70 +
        6447120347516446576348628795275991725501857932312943297203123445754813) * 10 ^ 70 +
        3833343933953923181915030688551532504725252350260330989643622014350673) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 202 = 29 +
      173 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_319_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_319_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Main_coeff_320_prefix_zero :
    (∑ x ∈ Finset.range 87,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (320 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (320 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_320_suffix_zero :
    (∑ x ∈ Finset.range 174,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (320 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_320 :
    recurrence2Scalar2Main.coeff 320 =
      -(((2542839945280669067068779188464862129 * 10 ^ 70 +
        6857849923422792389498570921546401530915180192915882748837986182681112) * 10 ^ 70 +
        4326370489746372772049067422101734539919500642544068242493471145099284) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 202 = 28 +
      174 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_320_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_320_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Main_coeff_321_prefix_zero :
    (∑ x ∈ Finset.range 88,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (321 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (321 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_321_suffix_zero :
    (∑ x ∈ Finset.range 175,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (321 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_321 :
    recurrence2Scalar2Main.coeff 321 =
      (((295948849442373561357637745468246236 * 10 ^ 70 +
        6579984425521036463205478091040163134742478981212887897483290523553486) * 10 ^ 70 +
        0263116087574954176364395147421694387111691756129375970903971006585724) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 202 = 27 +
      175 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_321_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_321_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Main_coeff_322_prefix_zero :
    (∑ x ∈ Finset.range 89,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (322 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (322 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_322_suffix_zero :
    (∑ x ∈ Finset.range 176,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (322 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_322 :
    recurrence2Scalar2Main.coeff 322 =
      -(((24710175853541087079412258605580274 * 10 ^ 70 +
        0721931195676762484002714807196424711226250580945101510293940982412232) * 10 ^ 70 +
        1827977440969843812306317149317808464663648373121335104737272936925142) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 202 = 26 +
      176 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_322_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_322_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Main_coeff_323_prefix_zero :
    (∑ x ∈ Finset.range 90,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (323 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (323 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_323_suffix_zero :
    (∑ x ∈ Finset.range 177,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (323 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_323 :
    recurrence2Scalar2Main.coeff 323 =
      (((1318067843596303020768019824171823 * 10 ^ 70 +
        4955282190335643988263266404502789172659911119371340205010922487843356) * 10 ^ 70 +
        3342963927825168248765157518894225136859643166183354123360205880495272) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 202 = 25 +
      177 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_323_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_323_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Main_coeff_324_prefix_zero :
    (∑ x ∈ Finset.range 91,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (324 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (324 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_324_suffix_zero :
    (∑ x ∈ Finset.range 178,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (324 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_324 :
    recurrence2Scalar2Main.coeff 324 =
      -(((3440268919530050578897182983972 * 10 ^ 70 +
        7594123071135407788648519926287338364974265920186339717689481945214392) * 10 ^ 70 +
        9009862114180293073463305944877940585635150377962733642110885957196739) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 202 = 24 +
      178 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_324_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_324_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Main_coeff_325_prefix_zero :
    (∑ x ∈ Finset.range 92,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (325 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (325 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_325_suffix_zero :
    (∑ x ∈ Finset.range 179,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (325 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_325 :
    recurrence2Scalar2Main.coeff 325 =
      -(((8612396978175425338299635825288 * 10 ^ 70 +
        7952397604936050040695237547512556002453747523208064048495573268117365) * 10 ^ 70 +
        5517516950473533206185401284673676909104151330845881785550274725559995) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 202 = 23 +
      179 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_325_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_325_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Main_coeff_326_prefix_zero :
    (∑ x ∈ Finset.range 93,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (326 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (326 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_326_suffix_zero :
    (∑ x ∈ Finset.range 180,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (326 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_326 :
    recurrence2Scalar2Main.coeff 326 =
      (((1137800376346997074717370633265 * 10 ^ 70 +
        6270307366110326573780707870135769021608089403559152068625159929994570) * 10 ^ 70 +
        1109204244692620464787811483283567230180240331324369300644546239875809) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 202 = 22 +
      180 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_326_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_326_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Main_coeff_327_prefix_zero :
    (∑ x ∈ Finset.range 94,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (327 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (327 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_327_suffix_zero :
    (∑ x ∈ Finset.range 181,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (327 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_327 :
    recurrence2Scalar2Main.coeff 327 =
      -(((91113373652381188597690792524 * 10 ^ 70 +
        1231599359758260903058147361686587757964822111519295372480622311096432) * 10 ^ 70 +
        3412942152055605559285595920246158234756362922431446171562884353253148) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 202 = 21 +
      181 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_327_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_327_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Main_coeff_328_prefix_zero :
    (∑ x ∈ Finset.range 95,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (328 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (328 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_328_suffix_zero :
    (∑ x ∈ Finset.range 182,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (328 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_328 :
    recurrence2Scalar2Main.coeff 328 =
      (((4854101435780678867137455408 * 10 ^ 70 +
        6958051198896089101005677151646466941692374100146289079919406125039712) * 10 ^ 70 +
        1915634390641031943100230466982689542846080894929449585641126981106982) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 202 = 20 +
      182 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_328_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_328_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Main_coeff_329_prefix_zero :
    (∑ x ∈ Finset.range 96,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (329 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (329 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_329_suffix_zero :
    (∑ x ∈ Finset.range 183,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (329 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_329 :
    recurrence2Scalar2Main.coeff 329 =
      -(((129484358716314561343049955 * 10 ^ 70 +
        5248290170096731013173709481002911288764758523226392088073889950400273) * 10 ^ 70 +
        5617462862894627022773460538635769623325604119233950363490147015244871) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 202 = 19 +
      183 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_329_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_329_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Main_coeff_330_prefix_zero :
    (∑ x ∈ Finset.range 97,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (330 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (330 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_330_suffix_zero :
    (∑ x ∈ Finset.range 184,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (330 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_330 :
    recurrence2Scalar2Main.coeff 330 =
      -(((4834140668658228414622796 * 10 ^ 70 +
        2381709052288710624763333875077545610257970186017344995258530784940248) * 10 ^ 70 +
        8809803769509955877999670913271053538038894234458522808266203367822030) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 202 = 18 +
      184 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_330_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_330_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Main_coeff_331_prefix_zero :
    (∑ x ∈ Finset.range 98,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (331 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (331 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_331_suffix_zero :
    (∑ x ∈ Finset.range 185,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (331 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_331 :
    recurrence2Scalar2Main.coeff 331 =
      (((812470723025451525638503 * 10 ^ 70 +
        0714266932153122161568777010869412299690523606483276697276677210589086) * 10 ^ 70 +
        5615215207595992939558384408823771199612657979247605745420280810932009) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 202 = 17 +
      185 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_331_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_331_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Main_coeff_332_prefix_zero :
    (∑ x ∈ Finset.range 99,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (332 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (332 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_332_suffix_zero :
    (∑ x ∈ Finset.range 186,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (332 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_332 :
    recurrence2Scalar2Main.coeff 332 =
      -(((51781133944453125770478 * 10 ^ 70 +
        2018884291292624209460456316632194113853888774350251383030210678397435) * 10 ^ 70 +
        8140836888662381089748873835881246055735220846084241528215786095279184) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 202 = 16 +
      186 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_332_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_332_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Main_coeff_333_prefix_zero :
    (∑ x ∈ Finset.range 100,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (333 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (333 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_333_suffix_zero :
    (∑ x ∈ Finset.range 187,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (333 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_333 :
    recurrence2Scalar2Main.coeff 333 =
      (((1933271236309310659642 * 10 ^ 70 +
        4358302118899262565506374346696887937381918037156248304679024788282996) * 10 ^ 70 +
        5590257062998279798213994455944998277593251919053449117227180812887720) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 202 = 15 +
      187 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_333_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_333_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Main_coeff_334_prefix_zero :
    (∑ x ∈ Finset.range 101,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (334 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (334 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_334_suffix_zero :
    (∑ x ∈ Finset.range 188,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (334 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_334 :
    recurrence2Scalar2Main.coeff 334 =
      -(((29788584645904823362 * 10 ^ 70 +
        5921042944680545484185039213940110634970834429435250646879398366463319) * 10 ^ 70 +
        1697767399389660911661252438723971863870519912154999836886104977962603) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 202 = 14 +
      188 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_334_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_334_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Main_coeff_335_prefix_zero :
    (∑ x ∈ Finset.range 102,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (335 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (335 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_335_suffix_zero :
    (∑ x ∈ Finset.range 189,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (335 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_335 :
    recurrence2Scalar2Main.coeff 335 =
      -(((1216519198774344766 * 10 ^ 70 +
        6646633470664584609493074557394472002154989818695760980301716601851023) * 10 ^ 70 +
        6108598999330270694330817342780544502405429634534461022920093523208390) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 202 = 13 +
      189 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_335_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_335_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Main_coeff_336_prefix_zero :
    (∑ x ∈ Finset.range 103,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (336 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (336 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_336_suffix_zero :
    (∑ x ∈ Finset.range 190,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (336 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_336 :
    recurrence2Scalar2Main.coeff 336 =
      (((98711194334625607 * 10 ^ 70 +
        0239722173047649738846032839511052751195331784676158871118841948302414) * 10 ^ 70 +
        5043221868932920126344327952838464598915450543025680109667129642048246) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 202 = 12 +
      190 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_336_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_336_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Main_coeff_337_prefix_zero :
    (∑ x ∈ Finset.range 104,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (337 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (337 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_337_suffix_zero :
    (∑ x ∈ Finset.range 191,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (337 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_337 :
    recurrence2Scalar2Main.coeff 337 =
      -(((3168224069642583 * 10 ^ 70 +
        1654390563671621239163998895305793906581644684972735033235382671948268) * 10 ^ 70 +
        6692646703441075721880617125409359004249885537522571617712933216517669) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 202 = 11 +
      191 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_337_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_337_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
