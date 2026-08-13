/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB0
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupQuotientConstant
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar0MainPart1Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: Scalar0Main coefficient convolution

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence2B0_coeff_0
  recurrence2B0_coeff_1
  recurrence2B0_coeff_2
  recurrence2B0_coeff_3
  recurrence2B0_coeff_4
  recurrence2B0_coeff_5
  recurrence2B0_coeff_6
  recurrence2B0_coeff_7
  recurrence2B0_coeff_8
  recurrence2B0_coeff_9
  recurrence2B0_coeff_10
  recurrence2B0_coeff_11
  recurrence2B0_coeff_12
  recurrence2B0_coeff_13
  recurrence2B0_coeff_14
  recurrence2B0_coeff_15
  recurrence2B0_coeff_16
  recurrence2B0_coeff_17
  recurrence2B0_coeff_18
  recurrence2B0_coeff_19
  recurrence2B0_coeff_20
  recurrence2B0_coeff_21
  recurrence2B0_coeff_22
  recurrence2B0_coeff_23
  recurrence2B0_coeff_24
  recurrence2B0_coeff_25
  recurrence2B0_coeff_26
  recurrence2B0_coeff_27
  recurrence2B0_coeff_28
  recurrence2B0_coeff_29
  recurrence2B0_coeff_30
  recurrence2B0_coeff_31
  recurrence2B0_coeff_32
  recurrence2B0_coeff_33
  recurrence2B0_coeff_34
  recurrence2B0_coeff_35
  recurrence2B0_coeff_36
  recurrence2B0_coeff_37
  recurrence2B0_coeff_38
  recurrence2B0_coeff_39
  recurrence2B0_coeff_40
  recurrence2B0_coeff_41
  recurrence2B0_coeff_42
  recurrence2B0_coeff_43
  recurrence2B0_coeff_44
  recurrence2B0_coeff_45
  recurrence2B0_coeff_46
  recurrence2B0_coeff_47
  recurrence2B0_coeff_48
  recurrence2B0_coeff_49
  recurrence2B0_coeff_50
  recurrence2B0_coeff_51
  recurrence2B0_coeff_52
  recurrence2B0_coeff_53
  recurrence2B0_coeff_54
  recurrence2B0_coeff_55
  recurrence2B0_coeff_56
  recurrence2B0_coeff_57
  recurrence2B0_coeff_58
  recurrence2B0_coeff_59
  recurrence2B0_coeff_60
  recurrence2B0_coeff_61
  recurrence2B0_coeff_62
  recurrence2B0_coeff_63
  recurrence2B0_coeff_64
  recurrence2B0_coeff_65
  recurrence2B0_coeff_66
  recurrence2B0_coeff_67
  recurrence2B0_coeff_68
  recurrence2B0_coeff_69
  recurrence2B0_coeff_70
  recurrence2B0_coeff_71
  recurrence2B0_coeff_72
  recurrence2B0_coeff_73
  recurrence2B0_coeff_74
  recurrence2B0_coeff_75
  recurrence2B0_coeff_76
  recurrence2B0_coeff_77
  recurrence2B0_coeff_78
  recurrence2B0_coeff_79
  recurrence2B0_coeff_80
  recurrence2B0_coeff_81
  recurrence2B0_coeff_82
  recurrence2B0_coeff_83
  recurrence2B0_coeff_84
  recurrence2B0_coeff_85
  recurrence2B0_coeff_86
  recurrence2B0_coeff_87
  recurrence2B0_coeff_88
  recurrence2B0_coeff_89
  recurrence2B0_coeff_90
  recurrence2B0_coeff_91
  recurrence2B0_coeff_92
  recurrence2B0_coeff_93
  recurrence2B0_coeff_94
  recurrence2B0_coeff_95
  recurrence2B0_coeff_96
  recurrence2B0_coeff_97
  recurrence2B0_coeff_98
  recurrence2B0_coeff_99
  recurrence2B0_coeff_100
  recurrence2B0_coeff_101
  recurrence2B0_coeff_102
  recurrence2B0_coeff_103
  recurrence2B0_coeff_104
  recurrence2B0_coeff_105
  recurrence2B0_coeff_106
  recurrence2B0_coeff_107
  recurrence2B0_coeff_108
  recurrence2B0_coeff_109
  recurrence2B0_coeff_110
  recurrence2B0_coeff_111
  recurrence2B0_coeff_112
  recurrence2B0_coeff_113
  recurrence2B0_coeff_114
  recurrence2B0_coeff_115
  recurrence2B0_coeff_116
  recurrence2B0_coeff_117
  recurrence2B0_coeff_118
  recurrence2B0_coeff_119
  recurrence2B0_coeff_120
  recurrence2B0_coeff_121
  recurrence2B0_coeff_122
  recurrence2B0_coeff_123
  recurrence2B0_coeff_124
  recurrence2B0_coeff_125
  recurrence2B0_coeff_126
  recurrence2B0_coeff_127
  recurrence2B0_coeff_128
  recurrence2B0_coeff_129
  recurrence2B0_coeff_130
  recurrence2B0_coeff_131
  recurrence2B0_coeff_132
  recurrence2B0_coeff_133
  recurrence2B0_coeff_134
  recurrence2B0_coeff_135
  recurrence2B0_coeff_136
  recurrence2B0_coeff_137
  recurrence2B0_coeff_138
  recurrence2B0_coeff_139
  recurrence2B0_coeff_140
  recurrence2B0_coeff_141
  recurrence2B0_coeff_142
  recurrence2B0_coeff_143
  recurrence2B0_coeff_144
  recurrence2B0_coeff_145
  recurrence2B0_coeff_146
  recurrence2B0_coeff_147
  recurrence2B0_coeff_148
  recurrence2B0_coeff_149
  recurrence2B0_coeff_150
  recurrence2B0_coeff_151
  recurrence2B0_coeff_152
  recurrence2B0_coeff_153
  recurrence2B0_coeff_154
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

private theorem recurrence2Scalar0Main_coeff_268_prefix_zero :
    (∑ x ∈ Finset.range 35,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (268 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (268 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_268_suffix_zero :
    (∑ x ∈ Finset.range 114,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (268 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_268 :
    recurrence2Scalar0Main.coeff 268 =
      (((6870643032497612720137139403832811975770178008172829323215465401307034 * 10 ^ 70 +
        6706064790296676322334506119255120011054819037899481690972383765791338) * 10 ^ 70 +
        6517103838095648563918720681927303451246031173926587767324778968202217) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 138 = 24 +
      114 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_268_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_268_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_269_prefix_zero :
    (∑ x ∈ Finset.range 36,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (269 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (269 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_269_suffix_zero :
    (∑ x ∈ Finset.range 115,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (269 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_269 :
    recurrence2Scalar0Main.coeff 269 =
      -(((9071434387300656744863555459653655696272927722143882437128733283644467 * 10 ^ 70 +
        4566390950982790959150910688914979475229467051001884813336967788346386) * 10 ^ 70 +
        9413967686542535769156146324921471843278347287784950955935136237258951) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 138 = 23 +
      115 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_269_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_269_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_270_prefix_zero :
    (∑ x ∈ Finset.range 37,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (270 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (270 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_270_suffix_zero :
    (∑ x ∈ Finset.range 116,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (270 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_270 :
    recurrence2Scalar0Main.coeff 270 =
      (((7784360680628956793131735795557513654924441229816721887391814400630805 * 10 ^ 70 +
        5268934654307807331844305836780320311054168154471951668527415871815336) * 10 ^ 70 +
        4579600813031736881418788098054886183616549578017895269647911335039165) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 138 = 22 +
      116 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_270_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_270_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_271_prefix_zero :
    (∑ x ∈ Finset.range 38,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (271 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (271 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_271_suffix_zero :
    (∑ x ∈ Finset.range 117,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (271 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_271 :
    recurrence2Scalar0Main.coeff 271 =
      -(((5604976650371474376379880576376658779658916765133176771140945538209514 * 10 ^ 70 +
        5157326342124548097649557506633774239389384888979168754094658954283624) * 10 ^ 70 +
        9508580103949126943201127940243209026815598763723748881347266273238519) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 138 = 21 +
      117 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_271_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_271_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_272_prefix_zero :
    (∑ x ∈ Finset.range 39,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (272 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (272 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_272_suffix_zero :
    (∑ x ∈ Finset.range 118,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (272 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_272 :
    recurrence2Scalar0Main.coeff 272 =
      (((3622553259906066889424506418547689926383054846880158178185792901791317 * 10 ^ 70 +
        4935702938454318635358596258036864852207871381323911711486594246778583) * 10 ^ 70 +
        1362885048673974242397394908522462145387966465540805667358152990636644) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 138 = 20 +
      118 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_272_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_272_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_273_prefix_zero :
    (∑ x ∈ Finset.range 40,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (273 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (273 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_273_suffix_zero :
    (∑ x ∈ Finset.range 119,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (273 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_273 :
    recurrence2Scalar0Main.coeff 273 =
      -(((2159688178277758047526019807965154288505186626792526134058619635622338 * 10 ^ 70 +
        3614229480392900016468489946760899471777073454011578069795470251414407) * 10 ^ 70 +
        1962469399766151106072618119056196944278037972657565659645307814019206) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 138 = 19 +
      119 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_273_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_273_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_274_prefix_zero :
    (∑ x ∈ Finset.range 41,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (274 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (274 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_274_suffix_zero :
    (∑ x ∈ Finset.range 120,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (274 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_274 :
    recurrence2Scalar0Main.coeff 274 =
      (((1203347489683287888957953205385859777245516979590849855438759541133748 * 10 ^ 70 +
        2930439327445779079837250740216779432924713482553709748740647258352692) * 10 ^ 70 +
        0584764071361317474218539116848847217023402938376904623340612906060559) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 138 = 18 +
      120 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_274_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_274_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_275_prefix_zero :
    (∑ x ∈ Finset.range 42,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (275 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (275 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_275_suffix_zero :
    (∑ x ∈ Finset.range 121,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (275 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_275 :
    recurrence2Scalar0Main.coeff 275 =
      -(((630771405318048481972067602271549906204938050848110075375812482958588 * 10 ^ 70 +
        7726122557723912330861936619375460892522404702606934832694033858652700) * 10 ^ 70 +
        3431987685775936435595929452901533258284489142227781636445266317077221) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 138 = 17 +
      121 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_275_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_275_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_276_prefix_zero :
    (∑ x ∈ Finset.range 43,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (276 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (276 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_276_suffix_zero :
    (∑ x ∈ Finset.range 122,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (276 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_276 :
    recurrence2Scalar0Main.coeff 276 =
      (((311953769888266717147477942570521185975924848239826865746194948865499 * 10 ^ 70 +
        1762462573200235078664770876461525133556949735687650108570779552643111) * 10 ^ 70 +
        1493714549259243065005926004948242584829727324542389929953419570321133) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rhs
    rw [show 138 = 16 +
      122 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_276_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_276_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_277_prefix_zero :
    (∑ x ∈ Finset.range 44,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (277 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (277 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_277_suffix_zero :
    (∑ x ∈ Finset.range 123,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (277 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_277 :
    recurrence2Scalar0Main.coeff 277 =
      -(((145604581248372129386812402506973918140659423630959632675351338358781 * 10 ^ 70 +
        8321869236028508583966519334523639351630966649298737428696263348397424) * 10 ^ 70 +
        0154263690775478128850155453268049513605285672601522607651863994875119) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 170 = 32 +
      138 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 138 = 15 +
      123 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_277_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_277_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_278_prefix_zero :
    (∑ x ∈ Finset.range 45,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (278 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (278 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_278_suffix_zero :
    (∑ x ∈ Finset.range 124,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (278 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_278 :
    recurrence2Scalar0Main.coeff 278 =
      (((64006734341242971574752935971878136513861911660927771916620240939351 * 10 ^ 70 +
        2601481289635096651963133585809712798937660355635190777246587202744583) * 10 ^ 70 +
        1215539039081371684597369056486497067194742222944549336704003973959223) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 170 = 32 +
      138 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 138 = 14 +
      124 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_278_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_278_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_279_prefix_zero :
    (∑ x ∈ Finset.range 46,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (279 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (279 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_279_suffix_zero :
    (∑ x ∈ Finset.range 125,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (279 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_279 :
    recurrence2Scalar0Main.coeff 279 =
      -(((26369416302474511351991702748880017393273089324099884285134675597891 * 10 ^ 70 +
        5266576847865434303203009166034503743315758125070083311410671175047442) * 10 ^ 70 +
        3748460545676075023285344160668047515214769275631756721394531844818173) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 170 = 32 +
      138 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 138 = 13 +
      125 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_279_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_279_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_280_prefix_zero :
    (∑ x ∈ Finset.range 47,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (280 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (280 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_280_suffix_zero :
    (∑ x ∈ Finset.range 126,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (280 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_280 :
    recurrence2Scalar0Main.coeff 280 =
      (((10086711891390339920152031870044686181364857690164116189594240251699 * 10 ^ 70 +
        9348439547787775597771944771993773684971289844759351427091265533137027) * 10 ^ 70 +
        6636676847928423854384752174249993309212930257751708205576636145191940) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 170 = 32 +
      138 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 138 = 12 +
      126 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_280_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_280_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_281_prefix_zero :
    (∑ x ∈ Finset.range 48,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (281 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (281 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_281_suffix_zero :
    (∑ x ∈ Finset.range 127,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (281 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_281 :
    recurrence2Scalar0Main.coeff 281 =
      -(((3519748484627055095733648929967589934391789700090678298810900178720 * 10 ^ 70 +
        8374591445204420182580975743976620398330204720976641570045327032159103) * 10 ^ 70 +
        3400011328451092287629430749359060454322039995578450209370907402105662) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 170 = 32 +
      138 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 138 = 11 +
      127 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_281_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_281_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_282_prefix_zero :
    (∑ x ∈ Finset.range 49,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (282 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (282 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_282_suffix_zero :
    (∑ x ∈ Finset.range 128,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (282 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_282 :
    recurrence2Scalar0Main.coeff 282 =
      (((1079564085877134136723998565517131319684280730104779409712282076817 * 10 ^ 70 +
        1077084818343670440390971375715360080007685233729722709510187259228078) * 10 ^ 70 +
        1922115472540555049999126329407864272623513944903739075995024867060113) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 170 = 32 +
      138 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 138 = 10 +
      128 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_282_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_282_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_283_prefix_zero :
    (∑ x ∈ Finset.range 50,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (283 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (283 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_283_suffix_zero :
    (∑ x ∈ Finset.range 129,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (283 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_283 :
    recurrence2Scalar0Main.coeff 283 =
      -(((263407349636154058814144562936026495086998114725999877997771901168 * 10 ^ 70 +
        1149072376892070061793603850470071270436971347773299322520411234477687) * 10 ^ 70 +
        5242974994431394236906202176941885029857578675826304054528588077050354) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 170 = 32 +
      138 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 138 = 9 +
      129 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_283_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_283_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_284_prefix_zero :
    (∑ x ∈ Finset.range 51,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (284 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (284 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_284_suffix_zero :
    (∑ x ∈ Finset.range 130,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (284 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_284 :
    recurrence2Scalar0Main.coeff 284 =
      (((30477395520182675843988654389543872746318077054912011341912742984 * 10 ^ 70 +
        1702606917801647236581350701935859504071842048182584388778858630478480) * 10 ^ 70 +
        5124805223213335591722641509482598875223415338912436396735686850051336) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 170 = 32 +
      138 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 138 = 8 +
      130 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_284_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_284_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_285_prefix_zero :
    (∑ x ∈ Finset.range 52,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (285 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (285 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_285_suffix_zero :
    (∑ x ∈ Finset.range 131,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (285 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_285 :
    recurrence2Scalar0Main.coeff 285 =
      (((17301001199843862706153986063753502122977456998342451463416857112 * 10 ^ 70 +
        4126015312668081890840233786402741481654441045253520054628773067072119) * 10 ^ 70 +
        6334629579689325222475213362517279812425508156878422301254296795901296) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 170 = 32 +
      138 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 138 = 7 +
      131 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_285_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_285_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_286_prefix_zero :
    (∑ x ∈ Finset.range 53,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (286 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (286 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_286_suffix_zero :
    (∑ x ∈ Finset.range 132,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (286 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_286 :
    recurrence2Scalar0Main.coeff 286 =
      -(((17178154592780384998740643324907948572015133276940751405438051520 * 10 ^ 70 +
        5412385252370748036626740553617352131931467996316932681308930441470996) * 10 ^ 70 +
        8600523473073083657017097153493940455012554742969319739475725680001052) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 170 = 32 +
      138 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 138 = 6 +
      132 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_286_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_286_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_287_prefix_zero :
    (∑ x ∈ Finset.range 54,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (287 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (287 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_287_suffix_zero :
    (∑ x ∈ Finset.range 133,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (287 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_287 :
    recurrence2Scalar0Main.coeff 287 =
      (((9929703527666010514941471965666723471973824455249250854178818089 * 10 ^ 70 +
        4136047052029975235570529817672046740723795502112864061784792651726503) * 10 ^ 70 +
        3419010948089986687413684408346488492790178522458445204046773879551327) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 170 = 32 +
      138 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 138 = 5 +
      133 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_287_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_287_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_288_prefix_zero :
    (∑ x ∈ Finset.range 55,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (288 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (288 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_288_suffix_zero :
    (∑ x ∈ Finset.range 134,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (288 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_288 :
    recurrence2Scalar0Main.coeff 288 =
      -(((4680148133363474962101062671456464445807973340379341567015428044 * 10 ^ 70 +
        8554625344379381999598935315266900413570014327648109146664971503426500) * 10 ^ 70 +
        1513188449782906450793551053434492477812565854369094805303017026604018) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 170 = 32 +
      138 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 138 = 4 +
      134 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_288_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_288_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_289_prefix_zero :
    (∑ x ∈ Finset.range 56,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (289 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (289 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_289_suffix_zero :
    (∑ x ∈ Finset.range 135,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (289 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_289 :
    recurrence2Scalar0Main.coeff 289 =
      (((1944997934105728537909809995611517141461732941123764436521561704 * 10 ^ 70 +
        8109290584156085365518165091725180470705939599582360509159328976823836) * 10 ^ 70 +
        2802978947759630986301628026897191717422505666906833224913108444042996) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 170 = 32 +
      138 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 138 = 3 +
      135 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_289_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_289_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_290_prefix_zero :
    (∑ x ∈ Finset.range 57,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (290 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (290 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_290_suffix_zero :
    (∑ x ∈ Finset.range 136,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (290 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_290 :
    recurrence2Scalar0Main.coeff 290 =
      -(((733974574886567282986683383747595472709445500679865091926735381 * 10 ^ 70 +
        0126879366688948754946602258099250948770167765880769801555423434755902) * 10 ^ 70 +
        0792211523090302576898045521686149682586393223055811334436388494635396) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 170 = 32 +
      138 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 138 = 2 +
      136 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_290_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_290_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_291_prefix_zero :
    (∑ x ∈ Finset.range 58,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (291 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (291 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_291_suffix_zero :
    (∑ x ∈ Finset.range 137,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (291 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_291 :
    recurrence2Scalar0Main.coeff 291 =
      (((254671040299420473204591633502579877201283114421646402002725452 * 10 ^ 70 +
        6122890686777948410325080221531922817704211097021325593371127781029381) * 10 ^ 70 +
        7937438473667589757903249724237760208160825759247477191321015129281722) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 170 = 32 +
      138 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 138 = 1 +
      137 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_291_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_291_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_292_prefix_zero :
    (∑ x ∈ Finset.range 59,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (292 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (292 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_292_suffix_zero :
    (∑ x ∈ Finset.range 138,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (292 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_292 :
    recurrence2Scalar0Main.coeff 292 =
      -(((81593028949653090281270595771581161489834691957189004617452734 * 10 ^ 70 +
        8740050445443998310654165311758808224510420575647566077172756667400059) * 10 ^ 70 +
        0257160621962575265983268053606686343995813407673148775753829904323024) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 170 = 32 +
      138 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_292_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_292_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_293_prefix_zero :
    (∑ x ∈ Finset.range 60,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (293 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (293 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_293_suffix_zero :
    (∑ x ∈ Finset.range 139,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (293 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_293 :
    recurrence2Scalar0Main.coeff 293 =
      (((24099865582317701893924815582463473987980984509607503779385974 * 10 ^ 70 +
        5733536795676130339256588917408792286925767502264809368440505627557103) * 10 ^ 70 +
        9473246119155456136462154001144564252449930395269306869790542449803266) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 170 = 31 +
      139 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_293_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_293_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_294_prefix_zero :
    (∑ x ∈ Finset.range 61,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (294 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (294 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_294_suffix_zero :
    (∑ x ∈ Finset.range 140,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (294 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_294 :
    recurrence2Scalar0Main.coeff 294 =
      -(((6511268119406283555776388124009803224172422892242288006782774 * 10 ^ 70 +
        8919900950714033111316609283824498033240389906160445338708808259427533) * 10 ^ 70 +
        1026990192570381956923576121523238499828681822819993925465313538502329) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 170 = 30 +
      140 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_294_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_294_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_295_prefix_zero :
    (∑ x ∈ Finset.range 62,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (295 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (295 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_295_suffix_zero :
    (∑ x ∈ Finset.range 141,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (295 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_295 :
    recurrence2Scalar0Main.coeff 295 =
      (((1580654746257439644642123268254651016784049223594536303254188 * 10 ^ 70 +
        4192989454369146200606583951279314513867982102526250614094996427133008) * 10 ^ 70 +
        1055624806320628061799433154622938099631930335756066664677827394119388) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 170 = 29 +
      141 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_295_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_295_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_296_prefix_zero :
    (∑ x ∈ Finset.range 63,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (296 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (296 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_296_suffix_zero :
    (∑ x ∈ Finset.range 142,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (296 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_296 :
    recurrence2Scalar0Main.coeff 296 =
      -(((331029945764984284118625013025765917109799284645317600102965 * 10 ^ 70 +
        8295582293446904385381647051025251403625517882733351735379123766883565) * 10 ^ 70 +
        6118085996046015451912764778266475760678537310228505541250039827932613) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 170 = 28 +
      142 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_296_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_296_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_297_prefix_zero :
    (∑ x ∈ Finset.range 64,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (297 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (297 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_297_suffix_zero :
    (∑ x ∈ Finset.range 143,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (297 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_297 :
    recurrence2Scalar0Main.coeff 297 =
      (((53235201465267519004670129727661666239896239344454807186552 * 10 ^ 70 +
        6287021945900015696822241981793726499409516379338978969858234796428961) * 10 ^ 70 +
        1592637822751981067589362119742361204033176315977283147458297036651851) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 170 = 27 +
      143 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_297_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_297_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_298_prefix_zero :
    (∑ x ∈ Finset.range 65,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (298 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (298 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_298_suffix_zero :
    (∑ x ∈ Finset.range 144,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (298 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_298 :
    recurrence2Scalar0Main.coeff 298 =
      -(((3144252444646942841387116669200278502064066484062521972717 * 10 ^ 70 +
        3526201375703888149882438616122259706718182754997096029767353009110811) * 10 ^ 70 +
        1855182248129437285389852483669611816824903889245032959012618134293364) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 170 = 26 +
      144 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_298_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_298_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_299_prefix_zero :
    (∑ x ∈ Finset.range 66,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (299 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (299 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_299_suffix_zero :
    (∑ x ∈ Finset.range 145,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (299 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_299 :
    recurrence2Scalar0Main.coeff 299 =
      -(((2135340135035202905643303046878075278796827884143284796881 * 10 ^ 70 +
        5377261460185399929594158529296717984894674185566004352452889572906055) * 10 ^ 70 +
        7916289920018892599218493157010124363441204972564364556655859752470018) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 170 = 25 +
      145 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_299_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_299_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_300_prefix_zero :
    (∑ x ∈ Finset.range 67,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (300 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (300 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_300_suffix_zero :
    (∑ x ∈ Finset.range 146,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (300 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_300 :
    recurrence2Scalar0Main.coeff 300 =
      (((1251544805318809853035600967582555144135645295272356658026 * 10 ^ 70 +
        5279345292206038255658913409593688244508230022670858852506426717540268) * 10 ^ 70 +
        4843686839280733773361019758099206362461879900807862424031247222533647) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 170 = 24 +
      146 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_300_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_300_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_301_prefix_zero :
    (∑ x ∈ Finset.range 68,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (301 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (301 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_301_suffix_zero :
    (∑ x ∈ Finset.range 147,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (301 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_301 :
    recurrence2Scalar0Main.coeff 301 =
      -(((460914529475600899294457360596956373883439685344912438788 * 10 ^ 70 +
        2549679930242450445341474923372934891440541883075078499285757279463513) * 10 ^ 70 +
        5615621487693622521883342272478558072753333554788471683534787547493126) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 170 = 23 +
      147 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_301_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_301_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_302_prefix_zero :
    (∑ x ∈ Finset.range 69,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (302 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (302 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_302_suffix_zero :
    (∑ x ∈ Finset.range 148,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (302 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_302 :
    recurrence2Scalar0Main.coeff 302 =
      (((138698043645754279153869522259711334642013391616701815919 * 10 ^ 70 +
        0574383965645823312058696380856295591116109781617376417261893444686538) * 10 ^ 70 +
        7916638240672625289222870498659028147157567327298197831485913514893727) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 170 = 22 +
      148 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_302_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_302_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
