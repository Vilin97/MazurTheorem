/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB1
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB5A6
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar2ShiftPart1Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: Scalar2Shift coefficient convolution

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence2B1_coeff_0
  recurrence2B1_coeff_1
  recurrence2B1_coeff_2
  recurrence2B1_coeff_3
  recurrence2B1_coeff_4
  recurrence2B1_coeff_5
  recurrence2B1_coeff_6
  recurrence2B1_coeff_7
  recurrence2B1_coeff_8
  recurrence2B1_coeff_9
  recurrence2B1_coeff_10
  recurrence2B1_coeff_11
  recurrence2B1_coeff_12
  recurrence2B1_coeff_13
  recurrence2B1_coeff_14
  recurrence2B1_coeff_15
  recurrence2B1_coeff_16
  recurrence2B1_coeff_17
  recurrence2B1_coeff_18
  recurrence2B1_coeff_19
  recurrence2B1_coeff_20
  recurrence2B1_coeff_21
  recurrence2B1_coeff_22
  recurrence2B1_coeff_23
  recurrence2B1_coeff_24
  recurrence2B1_coeff_25
  recurrence2B1_coeff_26
  recurrence2B1_coeff_27
  recurrence2B1_coeff_28
  recurrence2B1_coeff_29
  recurrence2B1_coeff_30
  recurrence2B1_coeff_31
  recurrence2B1_coeff_32
  recurrence2B1_coeff_33
  recurrence2B1_coeff_34
  recurrence2B1_coeff_35
  recurrence2B1_coeff_36
  recurrence2B1_coeff_37
  recurrence2B1_coeff_38
  recurrence2B1_coeff_39
  recurrence2B1_coeff_40
  recurrence2B1_coeff_41
  recurrence2B1_coeff_42
  recurrence2B1_coeff_43
  recurrence2B1_coeff_44
  recurrence2B1_coeff_45
  recurrence2B1_coeff_46
  recurrence2B1_coeff_47
  recurrence2B1_coeff_48
  recurrence2B1_coeff_49
  recurrence2B1_coeff_50
  recurrence2B1_coeff_51
  recurrence2B1_coeff_52
  recurrence2B1_coeff_53
  recurrence2B1_coeff_54
  recurrence2B1_coeff_55
  recurrence2B1_coeff_56
  recurrence2B1_coeff_57
  recurrence2B1_coeff_58
  recurrence2B1_coeff_59
  recurrence2B1_coeff_60
  recurrence2B1_coeff_61
  recurrence2B1_coeff_62
  recurrence2B1_coeff_63
  recurrence2B1_coeff_64
  recurrence2B1_coeff_65
  recurrence2B1_coeff_66
  recurrence2B1_coeff_67
  recurrence2B1_coeff_68
  recurrence2B1_coeff_69
  recurrence2B1_coeff_70
  recurrence2B1_coeff_71
  recurrence2B1_coeff_72
  recurrence2B1_coeff_73
  recurrence2B1_coeff_74
  recurrence2B1_coeff_75
  recurrence2B1_coeff_76
  recurrence2B1_coeff_77
  recurrence2B1_coeff_78
  recurrence2B1_coeff_79
  recurrence2B1_coeff_80
  recurrence2B1_coeff_81
  recurrence2B1_coeff_82
  recurrence2B1_coeff_83
  recurrence2B1_coeff_84
  recurrence2B1_coeff_85
  recurrence2B1_coeff_86
  recurrence2B1_coeff_87
  recurrence2B1_coeff_88
  recurrence2B1_coeff_89
  recurrence2B1_coeff_90
  recurrence2B1_coeff_91
  recurrence2B1_coeff_92
  recurrence2B1_coeff_93
  recurrence2B1_coeff_94
  recurrence2B1_coeff_95
  recurrence2B1_coeff_96
  recurrence2B1_coeff_97
  recurrence2B1_coeff_98
  recurrence2B1_coeff_99
  recurrence2B1_coeff_100
  recurrence2B1_coeff_101
  recurrence2B1_coeff_102
  recurrence2B1_coeff_103
  recurrence2B1_coeff_104
  recurrence2B1_coeff_105
  recurrence2B1_coeff_106
  recurrence2B1_coeff_107
  recurrence2B1_coeff_108
  recurrence2B1_coeff_109
  recurrence2B1_coeff_110
  recurrence2B1_coeff_111
  recurrence2B1_coeff_112
  recurrence2B1_coeff_113
  recurrence2B1_coeff_114
  recurrence2B1_coeff_115
  recurrence2B1_coeff_116
  recurrence2B1_coeff_117
  recurrence2B1_coeff_118
  recurrence2B1_coeff_119
  recurrence2B1_coeff_120
  recurrence2B1_coeff_121
  recurrence2B1_coeff_122
  recurrence2B1_coeff_123
  recurrence2B1_coeff_124
  recurrence2B1_coeff_125
  recurrence2B1_coeff_126
  recurrence2B1_coeff_127
  recurrence2B1_coeff_128
  recurrence2B1_coeff_129
  recurrence2B1_coeff_130
  recurrence2B1_coeff_131
  recurrence2B1_coeff_132
  recurrence2B1_coeff_133
  recurrence2B1_coeff_134
  recurrence2B1_coeff_135
  recurrence2B1_coeff_136
  recurrence2B1_coeff_137
  recurrence2B1_coeff_138
  recurrence2B1_coeff_139
  recurrence2B1_coeff_140
  recurrence2B1_coeff_141
  recurrence2B1_coeff_142
  recurrence2B1_coeff_143
  recurrence2B1_coeff_144
  recurrence2B1_coeff_145
  recurrence2B1_coeff_146
  recurrence2B1_coeff_147
  recurrence2B1_coeff_148
  recurrence2B1_coeff_149
  recurrence2B1_coeff_150
  recurrence2B5A6_coeff_0
  recurrence2B5A6_coeff_1
  recurrence2B5A6_coeff_2
  recurrence2B5A6_coeff_3
  recurrence2B5A6_coeff_4
  recurrence2B5A6_coeff_5
  recurrence2B5A6_coeff_6
  recurrence2B5A6_coeff_7
  recurrence2B5A6_coeff_8
  recurrence2B5A6_coeff_9
  recurrence2B5A6_coeff_10
  recurrence2B5A6_coeff_11
  recurrence2B5A6_coeff_12
  recurrence2B5A6_coeff_13
  recurrence2B5A6_coeff_14
  recurrence2B5A6_coeff_15
  recurrence2B5A6_coeff_16
  recurrence2B5A6_coeff_17
  recurrence2B5A6_coeff_18
  recurrence2B5A6_coeff_19
  recurrence2B5A6_coeff_20
  recurrence2B5A6_coeff_21
  recurrence2B5A6_coeff_22
  recurrence2B5A6_coeff_23
  recurrence2B5A6_coeff_24
  recurrence2B5A6_coeff_25
  recurrence2B5A6_coeff_26
  recurrence2B5A6_coeff_27
  recurrence2B5A6_coeff_28
  recurrence2B5A6_coeff_29
  recurrence2B5A6_coeff_30
  recurrence2B5A6_coeff_31
  recurrence2B5A6_coeff_32
  recurrence2B5A6_coeff_33
  recurrence2B5A6_coeff_34
  recurrence2B5A6_coeff_35
  recurrence2B5A6_coeff_36
  recurrence2B5A6_coeff_37
  recurrence2B5A6_coeff_38
  recurrence2B5A6_coeff_39
  recurrence2B5A6_coeff_40
  recurrence2B5A6_coeff_41
  recurrence2B5A6_coeff_42
  recurrence2B5A6_coeff_43
  recurrence2B5A6_coeff_44
  recurrence2B5A6_coeff_45
  recurrence2B5A6_coeff_46
  recurrence2B5A6_coeff_47
  recurrence2B5A6_coeff_48
  recurrence2B5A6_coeff_49
  recurrence2B5A6_coeff_50
  recurrence2B5A6_coeff_51
  recurrence2B5A6_coeff_52
  recurrence2B5A6_coeff_53
  recurrence2B5A6_coeff_54
  recurrence2B5A6_coeff_55
  recurrence2B5A6_coeff_56
  recurrence2B5A6_coeff_57
  recurrence2B5A6_coeff_58
  recurrence2B5A6_coeff_59
  recurrence2B5A6_coeff_60
  recurrence2B5A6_coeff_61
  recurrence2B5A6_coeff_62
  recurrence2B5A6_coeff_63
  recurrence2B5A6_coeff_64
  recurrence2B5A6_coeff_65
  recurrence2B5A6_coeff_66
  recurrence2B5A6_coeff_67
  recurrence2B5A6_coeff_68
  recurrence2B5A6_coeff_69
  recurrence2B5A6_coeff_70
  recurrence2B5A6_coeff_71
  recurrence2B5A6_coeff_72
  recurrence2B5A6_coeff_73
  recurrence2B5A6_coeff_74
  recurrence2B5A6_coeff_75
  recurrence2B5A6_coeff_76
  recurrence2B5A6_coeff_77
  recurrence2B5A6_coeff_78
  recurrence2B5A6_coeff_79
  recurrence2B5A6_coeff_80
  recurrence2B5A6_coeff_81
  recurrence2B5A6_coeff_82
  recurrence2B5A6_coeff_83
  recurrence2B5A6_coeff_84
  recurrence2B5A6_coeff_85
  recurrence2B5A6_coeff_86
  recurrence2B5A6_coeff_87
  recurrence2B5A6_coeff_88
  recurrence2B5A6_coeff_89
  recurrence2B5A6_coeff_90
  recurrence2B5A6_coeff_91
  recurrence2B5A6_coeff_92
  recurrence2B5A6_coeff_93
  recurrence2B5A6_coeff_94
  recurrence2B5A6_coeff_95
  recurrence2B5A6_coeff_96
  recurrence2B5A6_coeff_97
  recurrence2B5A6_coeff_98
  recurrence2B5A6_coeff_99
  recurrence2B5A6_coeff_100
  recurrence2B5A6_coeff_101
  recurrence2B5A6_coeff_102
  recurrence2B5A6_coeff_103
  recurrence2B5A6_coeff_104
  recurrence2B5A6_coeff_105
  recurrence2B5A6_coeff_106
  recurrence2B5A6_coeff_107
  recurrence2B5A6_coeff_108
  recurrence2B5A6_coeff_109
  recurrence2B5A6_coeff_110
  recurrence2B5A6_coeff_111
  recurrence2B5A6_coeff_112
  recurrence2B5A6_coeff_113
  recurrence2B5A6_coeff_114
  recurrence2B5A6_coeff_115
  recurrence2B5A6_coeff_116
  recurrence2B5A6_coeff_117
  recurrence2B5A6_coeff_118
  recurrence2B5A6_coeff_119
  recurrence2B5A6_coeff_120
  recurrence2B5A6_coeff_121
  recurrence2B5A6_coeff_122
  recurrence2B5A6_coeff_123
  recurrence2B5A6_coeff_124
  recurrence2B5A6_coeff_125
  recurrence2B5A6_coeff_126
  recurrence2B5A6_coeff_127
  recurrence2B5A6_coeff_128
  recurrence2B5A6_coeff_129
  recurrence2B5A6_coeff_130
  recurrence2B5A6_coeff_131
  recurrence2B5A6_coeff_132
  recurrence2B5A6_coeff_133
  recurrence2B5A6_coeff_134
  recurrence2B5A6_coeff_135
  recurrence2B5A6_coeff_136
  recurrence2B5A6_coeff_137
  recurrence2B5A6_coeff_138
  recurrence2B5A6_coeff_139
  recurrence2B5A6_coeff_140
  recurrence2B5A6_coeff_141
  recurrence2B5A6_coeff_142
  recurrence2B5A6_coeff_143
  recurrence2B5A6_coeff_144
  recurrence2B5A6_coeff_145
  recurrence2B5A6_coeff_146
  recurrence2B5A6_coeff_147
  recurrence2B5A6_coeff_148
  recurrence2B5A6_coeff_149
  recurrence2B5A6_coeff_150
  recurrence2B5A6_coeff_151
  recurrence2B5A6_coeff_152
  recurrence2B5A6_coeff_153
  recurrence2B5A6_coeff_154
  recurrence2B5A6_coeff_155
  recurrence2B5A6_coeff_156
  recurrence2B5A6_coeff_157
  recurrence2B5A6_coeff_158
  recurrence2B5A6_coeff_159
  recurrence2B5A6_coeff_160
  recurrence2B5A6_coeff_161
  recurrence2B5A6_coeff_162
  recurrence2B5A6_coeff_163
  recurrence2B5A6_coeff_164
  recurrence2B5A6_coeff_165
  recurrence2B5A6_coeff_166
  recurrence2B5A6_coeff_167
  recurrence2B5A6_coeff_168
  recurrence2B5A6_coeff_169
  recurrence2B5A6_coeff_170
  recurrence2B5A6_coeff_171
  recurrence2B5A6_coeff_172
  recurrence2B5A6_coeff_173
  recurrence2B5A6_coeff_174
  recurrence2B5A6_coeff_175
  recurrence2B5A6_coeff_176
  recurrence2B5A6_coeff_177
  recurrence2B5A6_coeff_178
  recurrence2B5A6_coeff_179
  recurrence2B5A6_coeff_180
  recurrence2B5A6_coeff_181
  recurrence2B5A6_coeff_182
  recurrence2B5A6_coeff_183
  recurrence2B5A6_coeff_184
  recurrence2B5A6_coeff_185
  recurrence2B5A6_coeff_186
  recurrence2B5A6_coeff_187
  recurrence2B5A6_coeff_188
  recurrence2B5A6_coeff_189
  recurrence2B5A6_coeff_190
  recurrence2B5A6_coeff_191
  recurrence2B5A6_coeff_192
  recurrence2B5A6_coeff_193
  recurrence2B5A6_coeff_194
  recurrence2B5A6_coeff_195
  recurrence2B5A6_coeff_196
  recurrence2B5A6_coeff_197
  recurrence2B5A6_coeff_198
  recurrence2B5A6_coeff_199
  recurrence2B5A6_coeff_200
  recurrence2B5A6_coeff_201
  recurrence2B5A6_coeff_202
  recurrence2B5A6_coeff_203
  recurrence2B5A6_coeff_204
  recurrence2B5A6_coeff_205
  recurrence2B5A6_coeff_206
  recurrence2B5A6_coeff_207
  recurrence2B5A6_coeff_208
  recurrence2B5A6_coeff_209
  recurrence2B5A6_coeff_210
  recurrence2B5A6_coeff_211
  recurrence2B5A6_coeff_212
  recurrence2B5A6_coeff_213
  recurrence2B5A6_coeff_214
  recurrence2B5A6_coeff_215
  recurrence2B5A6_coeff_216
  recurrence2B5A6_coeff_217
  recurrence2B5A6_coeff_218
  recurrence2B5A6_coeff_219
  recurrence2B5A6_coeff_220
  recurrence2B5A6_coeff_221
  recurrence2B5A6_coeff_222
  recurrence2B5A6_coeff_223
  recurrence2B5A6_coeff_224
  recurrence2B5A6_coeff_225
  recurrence2B5A6_coeff_226
  recurrence2B5A6_coeff_227
  recurrence2B5A6_coeff_228
  recurrence2B5A6_coeff_229

private theorem recurrence2Scalar2Shift_coeff_301_prefix_zero :
    (∑ x ∈ Finset.range 72,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (301 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (301 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_301_suffix_zero :
    (∑ x ∈ Finset.range 151,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (301 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_301 :
    recurrence2Scalar2Shift.coeff 301 =
      -(((308984761107351702072276557666125552507509314238114 * 10 ^ 70 +
        4116765914874078873554423309210855917217928884197955090750262315410804) * 10 ^ 70 +
        6286924977909789077253883868188357249894585107116947696072410579277033) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 302 = 72 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 15 +
      151 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_301_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_301_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Shift_coeff_302_prefix_zero :
    (∑ x ∈ Finset.range 73,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (302 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (302 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_302_suffix_zero :
    (∑ x ∈ Finset.range 152,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (302 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_302 :
    recurrence2Scalar2Shift.coeff 302 =
      (((56531109356958453874531121119323598325459748983966 * 10 ^ 70 +
        8316472959906479442332476946656867109838124538321817707018742359918171) * 10 ^ 70 +
        8066406139219832808766293792405957181339400972135857184254937033046232) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 303 = 73 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 14 +
      152 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_302_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_302_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Shift_coeff_303_prefix_zero :
    (∑ x ∈ Finset.range 74,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (303 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (303 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_303_suffix_zero :
    (∑ x ∈ Finset.range 153,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (303 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_303 :
    recurrence2Scalar2Shift.coeff 303 =
      -(((7544756191348171920929456221251964924730286781909 * 10 ^ 70 +
        2950150716553270286444822890883120730390972250145605857636141913576026) * 10 ^ 70 +
        3761886901368318984426454369039493321209082760776297243279346635278212) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 304 = 74 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 13 +
      153 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_303_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_303_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Shift_coeff_304_prefix_zero :
    (∑ x ∈ Finset.range 75,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (304 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (304 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_304_suffix_zero :
    (∑ x ∈ Finset.range 154,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (304 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_304 :
    recurrence2Scalar2Shift.coeff 304 =
      (((387380667874796710521320457194671748300738857128 * 10 ^ 70 +
        2091634420008123802251864738993649379815316313453366437042376799201194) * 10 ^ 70 +
        1822011167082817003517582399480634266011359199921605843608580857904590) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 305 = 75 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 12 +
      154 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_304_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_304_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Shift_coeff_305_prefix_zero :
    (∑ x ∈ Finset.range 76,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (305 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (305 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_305_suffix_zero :
    (∑ x ∈ Finset.range 155,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (305 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_305 :
    recurrence2Scalar2Shift.coeff 305 =
      (((159555135070741614655828881815535224123031875525 * 10 ^ 70 +
        7696059041571811926278595588189926128671543300947072995211029734439181) * 10 ^ 70 +
        7905495944488155896172107018974622542850413770905800237087762732192572) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 306 = 76 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 11 +
      155 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_305_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_305_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Shift_coeff_306_prefix_zero :
    (∑ x ∈ Finset.range 77,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (306 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (306 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_306_suffix_zero :
    (∑ x ∈ Finset.range 156,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (306 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_306 :
    recurrence2Scalar2Shift.coeff 306 =
      -(((68702290666267382153232313904396274235866057601 * 10 ^ 70 +
        7021140785149825760817480430482859031168684309635685736921926252159169) * 10 ^ 70 +
        4848297443980890621990537762309732557924477542347210991540872468508720) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 307 = 77 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 10 +
      156 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_306_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_306_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Shift_coeff_307_prefix_zero :
    (∑ x ∈ Finset.range 78,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (307 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (307 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_307_suffix_zero :
    (∑ x ∈ Finset.range 157,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (307 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_307 :
    recurrence2Scalar2Shift.coeff 307 =
      (((17149049075139393637146495841863569550378830320 * 10 ^ 70 +
        8381573722891833794045170378086597133351963052872924577183260376740194) * 10 ^ 70 +
        1741860589025847166479227923510907594436020581532827830274090940532810) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 308 = 78 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 9 +
      157 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_307_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_307_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Shift_coeff_308_prefix_zero :
    (∑ x ∈ Finset.range 79,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (308 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (308 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_308_suffix_zero :
    (∑ x ∈ Finset.range 158,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (308 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_308 :
    recurrence2Scalar2Shift.coeff 308 =
      -(((3245525526901188806512110997853544485644439413 * 10 ^ 70 +
        4998573619693989138344167545311364965022665241411066202539368622520535) * 10 ^ 70 +
        2832328357876301809005604769582749081945054335880280335554115066219173) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 309 = 79 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 8 +
      158 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_308_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_308_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Shift_coeff_309_prefix_zero :
    (∑ x ∈ Finset.range 80,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (309 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (309 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_309_suffix_zero :
    (∑ x ∈ Finset.range 159,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (309 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_309 :
    recurrence2Scalar2Shift.coeff 309 =
      (((481706024861809648528995913492470820104661990 * 10 ^ 70 +
        3773368187555274450903869050959203632605621251334527213901957045699693) * 10 ^ 70 +
        2650124013820675682282245062483239812558895509008327559077095170935481) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 310 = 80 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 7 +
      159 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_309_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_309_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Shift_coeff_310_prefix_zero :
    (∑ x ∈ Finset.range 81,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (310 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (310 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_310_suffix_zero :
    (∑ x ∈ Finset.range 160,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (310 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_310 :
    recurrence2Scalar2Shift.coeff 310 =
      -(((52059813765743852628365948970171631776348343 * 10 ^ 70 +
        8075348634891490799636986600321135991795557176058475034457172701031885) * 10 ^ 70 +
        4440823655813582594160177442275468745900523042764435677946777107596216) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 311 = 81 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 6 +
      160 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_310_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_310_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Shift_coeff_311_prefix_zero :
    (∑ x ∈ Finset.range 82,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (311 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (311 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_311_suffix_zero :
    (∑ x ∈ Finset.range 161,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (311 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_311 :
    recurrence2Scalar2Shift.coeff 311 =
      (((2433207032017117137571786631794502380034617 * 10 ^ 70 +
        3869829144524447137340178968027442130190556215130319814787030031442878) * 10 ^ 70 +
        0043494300965351079630564850098837114008184795338554355608573951235453) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 312 = 82 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 5 +
      161 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_311_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_311_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Shift_coeff_312_prefix_zero :
    (∑ x ∈ Finset.range 83,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (312 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (312 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_312_suffix_zero :
    (∑ x ∈ Finset.range 162,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (312 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_312 :
    recurrence2Scalar2Shift.coeff 312 =
      (((552253338483753230971940742182184109041044 * 10 ^ 70 +
        3260808331657794729910267747726535815334164664376155713289587852950759) * 10 ^ 70 +
        2408397929585044503289071487417892937877889719148890009603437478841343) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 313 = 83 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 4 +
      162 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_312_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_312_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Shift_coeff_313_prefix_zero :
    (∑ x ∈ Finset.range 84,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (313 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (313 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_313_suffix_zero :
    (∑ x ∈ Finset.range 163,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (313 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_313 :
    recurrence2Scalar2Shift.coeff 313 =
      -(((191316924085719770471773105292836587814895 * 10 ^ 70 +
        1477233637540735107050300345649276905851981780528575088819279363768364) * 10 ^ 70 +
        0508705477146453816208226159760507833056750526781210734579008145894063) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 314 = 84 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 3 +
      163 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_313_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_313_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Shift_coeff_314_prefix_zero :
    (∑ x ∈ Finset.range 85,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (314 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (314 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_314_suffix_zero :
    (∑ x ∈ Finset.range 164,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (314 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_314 :
    recurrence2Scalar2Shift.coeff 314 =
      (((35372006347470969764424346186130586463586 * 10 ^ 70 +
        5416904328157552745139622371491243713784456981892242337285504433663775) * 10 ^ 70 +
        1120236855636385185805699096343770516649227268866085753782295968706641) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 315 = 85 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 2 +
      164 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_314_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_314_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Shift_coeff_315_prefix_zero :
    (∑ x ∈ Finset.range 86,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (315 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (315 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_315_suffix_zero :
    (∑ x ∈ Finset.range 165,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (315 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_315 :
    recurrence2Scalar2Shift.coeff 315 =
      -(((4687691783439434701264128590790780063500 * 10 ^ 70 +
        9513347855353960634825700068642905487390277675974391053623717153125173) * 10 ^ 70 +
        2385079246905586379418379645470994455551345544634949218320864419220375) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 316 = 86 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 1 +
      165 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_315_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_315_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Shift_coeff_316_prefix_zero :
    (∑ x ∈ Finset.range 87,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (316 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (316 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_316_suffix_zero :
    (∑ x ∈ Finset.range 166,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (316 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_316 :
    recurrence2Scalar2Shift.coeff 316 =
      (((439117346704483048115107244616843087021 * 10 ^ 70 +
        6167517558429231058159161927920357276447022068307547887428612442376850) * 10 ^ 70 +
        2591159178637809445571734918006943021373079441727803506797780367074763) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 317 = 87 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_316_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_316_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Shift_coeff_317_prefix_zero :
    (∑ x ∈ Finset.range 88,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (317 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (317 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_317_suffix_zero :
    (∑ x ∈ Finset.range 167,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (317 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_317 :
    recurrence2Scalar2Shift.coeff 317 =
      -(((19682267087557350951279478090097942619 * 10 ^ 70 +
        9871152599794562337929624641592131467187783304486405449285797886162589) * 10 ^ 70 +
        3231958577541271222722875638303472788405219405432377988921778330144310) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 318 = 88 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 31 +
      167 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_317_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_317_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Shift_coeff_318_prefix_zero :
    (∑ x ∈ Finset.range 89,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (318 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (318 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_318_suffix_zero :
    (∑ x ∈ Finset.range 168,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (318 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_318 :
    recurrence2Scalar2Shift.coeff 318 =
      -(((2326210158239207663862690204725938040 * 10 ^ 70 +
        4898021237607022641794877533501001037849913017045592572730756641615882) * 10 ^ 70 +
        5524020885552983886641519386894244152008938453465199318498592570884982) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 319 = 89 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 30 +
      168 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_318_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_318_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Shift_coeff_319_prefix_zero :
    (∑ x ∈ Finset.range 90,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (319 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (319 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_319_suffix_zero :
    (∑ x ∈ Finset.range 169,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (319 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_319 :
    recurrence2Scalar2Shift.coeff 319 =
      (((702446444250908903225852632599603971 * 10 ^ 70 +
        3066908883895583051335865780549200622888620749158934321241640980960129) * 10 ^ 70 +
        5848574213447606071242001156368288630806221842676956076933277660610049) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 320 = 90 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 29 +
      169 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_319_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_319_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Shift_coeff_320_prefix_zero :
    (∑ x ∈ Finset.range 91,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (320 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (320 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_320_suffix_zero :
    (∑ x ∈ Finset.range 170,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (320 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_320 :
    recurrence2Scalar2Shift.coeff 320 =
      -(((99422209210133751821668422989127460 * 10 ^ 70 +
        1623978028687040045440283649118293809320862258881599861701205535142471) * 10 ^ 70 +
        8018120980144001408239338497868998714200841593965782327833309675058434) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 321 = 91 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 28 +
      170 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_320_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_320_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Shift_coeff_321_prefix_zero :
    (∑ x ∈ Finset.range 92,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (321 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (321 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_321_suffix_zero :
    (∑ x ∈ Finset.range 171,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (321 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_321 :
    recurrence2Scalar2Shift.coeff 321 =
      (((9374327130842815664345925489198151 * 10 ^ 70 +
        0407008103649330820304402064511619409455115853103170718915619842612087) * 10 ^ 70 +
        9639215219911845930661543516728279322599738696872529447828994037285196) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 322 = 92 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 27 +
      171 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_321_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_321_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Shift_coeff_322_prefix_zero :
    (∑ x ∈ Finset.range 93,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (322 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (322 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_322_suffix_zero :
    (∑ x ∈ Finset.range 172,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (322 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_322 :
    recurrence2Scalar2Shift.coeff 322 =
      -(((527770931051918216721934122690443 * 10 ^ 70 +
        6495069927212679012062925000509861669815221490611524410584122552301705) * 10 ^ 70 +
        7016139721406402658493316151853278548911400976725023317405993083828085) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 323 = 93 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 26 +
      172 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_322_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_322_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Shift_coeff_323_prefix_zero :
    (∑ x ∈ Finset.range 94,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (323 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (323 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_323_suffix_zero :
    (∑ x ∈ Finset.range 173,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (323 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_323 :
    recurrence2Scalar2Shift.coeff 323 =
      -(((4831186900238517649925686875102 * 10 ^ 70 +
        9719272068437578285670068465336807538863770375022658741930829441182007) * 10 ^ 70 +
        0475114684321079618524459650551711748682227850003698371766914645058800) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 324 = 94 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 25 +
      173 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_323_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_323_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Shift_coeff_324_prefix_zero :
    (∑ x ∈ Finset.range 95,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (324 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (324 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_324_suffix_zero :
    (∑ x ∈ Finset.range 174,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (324 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_324 :
    recurrence2Scalar2Shift.coeff 324 =
      (((5179095443412610486433425237779 * 10 ^ 70 +
        0991892921105293519106374072918471717489675623588866485722462927158611) * 10 ^ 70 +
        0856303977639058272880287090635799183008449368724831800344771826533351) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 325 = 95 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 24 +
      174 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_324_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_324_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Shift_coeff_325_prefix_zero :
    (∑ x ∈ Finset.range 96,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (325 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (325 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_325_suffix_zero :
    (∑ x ∈ Finset.range 175,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (325 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_325 :
    recurrence2Scalar2Shift.coeff 325 =
      -(((688560609863678863819723030329 * 10 ^ 70 +
        3686336797237342458385215730784315529602885874358881629107950201257175) * 10 ^ 70 +
        4280948168775818928906125876346804668257904500563115395159863796415462) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 326 = 96 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 23 +
      175 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_325_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_325_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Shift_coeff_326_prefix_zero :
    (∑ x ∈ Finset.range 97,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (326 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (326 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_326_suffix_zero :
    (∑ x ∈ Finset.range 176,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (326 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_326 :
    recurrence2Scalar2Shift.coeff 326 =
      (((55489993721153613290326674223 * 10 ^ 70 +
        8077194139110870451974413625050627124778409865526352229241924864070761) * 10 ^ 70 +
        0462792593391765566135041558536878666824191596842946944325027311463981) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 327 = 97 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 22 +
      176 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_326_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_326_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Shift_coeff_327_prefix_zero :
    (∑ x ∈ Finset.range 98,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (327 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (327 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_327_suffix_zero :
    (∑ x ∈ Finset.range 177,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (327 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_327 :
    recurrence2Scalar2Shift.coeff 327 =
      -(((2696997217982737922739758747 * 10 ^ 70 +
        8206548868280415927991922120391839994232261176709073145202668553286301) * 10 ^ 70 +
        9032007640423395782943053326948057001901645373661510091608869691330845) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 328 = 98 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 21 +
      177 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_327_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_327_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Shift_coeff_328_prefix_zero :
    (∑ x ∈ Finset.range 99,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (328 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (328 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_328_suffix_zero :
    (∑ x ∈ Finset.range 178,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (328 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_328 :
    recurrence2Scalar2Shift.coeff 328 =
      (((16539826368328404698973650 * 10 ^ 70 +
        7219012765741742283664578363035362823096872311543550226230865339631628) * 10 ^ 70 +
        9931381535146830633680470375131260819857996519710383218793319990688477) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 329 = 99 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 20 +
      178 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_328_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_328_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Shift_coeff_329_prefix_zero :
    (∑ x ∈ Finset.range 100,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (329 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (329 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_329_suffix_zero :
    (∑ x ∈ Finset.range 179,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (329 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_329 :
    recurrence2Scalar2Shift.coeff 329 =
      (((10608904176994182022051160 * 10 ^ 70 +
        5238515893417758346514938210014703947282117087829664143350191683763678) * 10 ^ 70 +
        2687452371452695322686209784714743067553647912074321433472031675314138) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 330 = 100 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 19 +
      179 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_329_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_329_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Shift_coeff_330_prefix_zero :
    (∑ x ∈ Finset.range 101,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (330 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (330 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_330_suffix_zero :
    (∑ x ∈ Finset.range 180,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (330 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_330 :
    recurrence2Scalar2Shift.coeff 330 =
      -(((1098230217067524219234117 * 10 ^ 70 +
        0832701535493644889222215137815601612248618322536932546639530050085237) * 10 ^ 70 +
        0239014009338948994443425650834983578248185630089096610225628342794058) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 331 = 101 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 18 +
      180 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_330_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_330_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Shift_coeff_331_prefix_zero :
    (∑ x ∈ Finset.range 102,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (331 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (331 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_331_suffix_zero :
    (∑ x ∈ Finset.range 181,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (331 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_331 :
    recurrence2Scalar2Shift.coeff 331 =
      (((61730037861214972356897 * 10 ^ 70 +
        7670779974175721622072331451350063519577108811745434266232993580206194) * 10 ^ 70 +
        1462151228522504023351144277142548269113391514605376760461183566824629) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 332 = 102 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 17 +
      181 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_331_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_331_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Shift_coeff_332_prefix_zero :
    (∑ x ∈ Finset.range 103,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (332 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (332 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_332_suffix_zero :
    (∑ x ∈ Finset.range 182,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (332 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_332 :
    recurrence2Scalar2Shift.coeff 332 =
      -(((1818859585508881544805 * 10 ^ 70 +
        8114633831259786331837490077521776498892273041456404035792614258144265) * 10 ^ 70 +
        8661011615392757543590286927919225782763658234902355269264931852674278) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 333 = 103 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 16 +
      182 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_332_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_332_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Shift_coeff_333_prefix_zero :
    (∑ x ∈ Finset.range 104,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (333 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (333 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_333_suffix_zero :
    (∑ x ∈ Finset.range 183,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (333 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_333 :
    recurrence2Scalar2Shift.coeff 333 =
      -(((18007146556516504884 * 10 ^ 70 +
        5297807813097462985415101148662278407820299047768087384910925825251240) * 10 ^ 70 +
        2528673481278790046667032504264084112574486670494498984814824045273328) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 334 = 104 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 15 +
      183 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_333_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_333_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Shift_coeff_334_prefix_zero :
    (∑ x ∈ Finset.range 105,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (334 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (334 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_334_suffix_zero :
    (∑ x ∈ Finset.range 184,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (334 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_334 :
    recurrence2Scalar2Shift.coeff 334 =
      (((4924469564155364067 * 10 ^ 70 +
        2774412947658833058114994007229914366427414041458956291634043707569307) * 10 ^ 70 +
        4839273396835234514608801128432044262450424747170712236489823984326647) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 335 = 105 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 14 +
      184 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_334_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_334_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Shift_coeff_335_prefix_zero :
    (∑ x ∈ Finset.range 106,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (335 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (335 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_335_suffix_zero :
    (∑ x ∈ Finset.range 185,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (335 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_335 :
    recurrence2Scalar2Shift.coeff 335 =
      -(((258701784841772862 * 10 ^ 70 +
        2801413076615569301493041318135533229774468441909551069072413500878601) * 10 ^ 70 +
        7857917252830296382607908205666493480165915970858196558108927835234134) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 336 = 106 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 13 +
      185 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_335_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_335_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Shift_coeff_336_prefix_zero :
    (∑ x ∈ Finset.range 107,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (336 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (336 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_336_suffix_zero :
    (∑ x ∈ Finset.range 186,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (336 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_336 :
    recurrence2Scalar2Shift.coeff 336 =
      (((6553731471795901 * 10 ^ 70 +
        7488093568946334491625027899028998469182070668326607201797126154378401) * 10 ^ 70 +
        6504905033126892418163682176215273690079010766514651285875351312160569) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 337 = 107 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 12 +
      186 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_336_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_336_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Shift_coeff_337_prefix_zero :
    (∑ x ∈ Finset.range 108,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (337 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (337 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_337_suffix_zero :
    (∑ x ∈ Finset.range 187,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (337 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_337 :
    recurrence2Scalar2Shift.coeff 337 =
      -(((4661966371210 * 10 ^ 70 +
        6358311362669926762088481247006399561379513501003755830676065553411314) * 10 ^ 70 +
        2915043026508386236816455701008223170500617146435178524940180894998275) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 338 = 108 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 11 +
      187 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_337_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_337_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
