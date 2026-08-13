/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB2
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB5A6
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar3ShiftPart0Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: Scalar3Shift coefficient convolution

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

private theorem recurrence2Scalar3Shift_coeff_194_suffix_zero :
    (∑ x ∈ Finset.range 48,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (194 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_194 :
    recurrence2Scalar3Shift.coeff 194 =
      (((19762268144938786622849578841354575201860504327868433579022110 * 10 ^ 70 +
        3675476426096230882903628345491194283747368691082318043854413897810205) * 10 ^ 70 +
        6571139213542922406815684455800719367169253989375308121181971830805599) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 195 = 0 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 19 +
      48 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_194_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_195_suffix_zero :
    (∑ x ∈ Finset.range 49,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (195 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_195 :
    recurrence2Scalar3Shift.coeff 195 =
      -(((61582361836249861564568135477175975416419091174344012287175397 * 10 ^ 70 +
        8521303957789580044530667087751901860064446695190971231176593388237066) * 10 ^ 70 +
        5817761429542373527961442047425524274030778927650398722040016570608601) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 196 = 0 +
    196 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 196 = 32 +
      164 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 164 = 32 +
      132 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 132 = 32 +
      100 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 100 = 32 +
      68 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 68 = 19 +
      49 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_195_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_196_suffix_zero :
    (∑ x ∈ Finset.range 50,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (196 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_196 :
    recurrence2Scalar3Shift.coeff 196 =
      (((118283494311998395512897354786840745724473789669730575012696058 * 10 ^ 70 +
        4453212018273758532540476853105965712922048632384591643092958323569680) * 10 ^ 70 +
        1441555040485425863166262267358811492352427807415359291919164420816636) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 197 = 0 +
    197 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 197 = 32 +
      165 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 19 +
      50 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_196_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_197_suffix_zero :
    (∑ x ∈ Finset.range 51,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (197 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_197 :
    recurrence2Scalar3Shift.coeff 197 =
      -(((93097788176188450082387905902690737484541051564634384396837355 * 10 ^ 70 +
        4655460846402576955787894822977528746584640063151148793023473367835754) * 10 ^ 70 +
        3711264070777055308313268934866798136747287394559126932879434453246709) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 198 = 0 +
    198 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 32 +
      102 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 102 = 32 +
      70 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 70 = 19 +
      51 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_197_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_198_suffix_zero :
    (∑ x ∈ Finset.range 52,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (198 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_198 :
    recurrence2Scalar3Shift.coeff 198 =
      -(((322237370454817762773830351793015017384912527841183858167777786 * 10 ^ 70 +
        8251895747878470868916194295940427177188338541691884771825883469248862) * 10 ^ 70 +
        6132186503128559763320072085348583995033866335577840379384265990436372) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 199 = 0 +
    199 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 199 = 32 +
      167 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 167 = 32 +
      135 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 19 +
      52 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_198_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_199_suffix_zero :
    (∑ x ∈ Finset.range 53,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (199 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_199 :
    recurrence2Scalar3Shift.coeff 199 =
      (((1759314091295987741221471843889458209596986961057910634213025417 * 10 ^ 70 +
        5079209000700474949886853952326818257188062484040458686960771488215790) * 10 ^ 70 +
        0047920426597838430856069020028044848797638849804572116960811814408549) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 200 = 0 +
    200 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 200 = 32 +
      168 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 168 = 32 +
      136 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 136 = 32 +
      104 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 104 = 32 +
      72 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 72 = 19 +
      53 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_199_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_200_suffix_zero :
    (∑ x ∈ Finset.range 54,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (200 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_200 :
    recurrence2Scalar3Shift.coeff 200 =
      -(((4962202977099505546130381528641322903979541039939358388151005688 * 10 ^ 70 +
        5264671845918721105914802813174939598479893988475831394836170260611722) * 10 ^ 70 +
        7249183621294223639427310808470180334632656515304702778991460509395775) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 201 = 0 +
    201 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 201 = 32 +
      169 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 32 +
      73 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 73 = 19 +
      54 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_200_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_201_suffix_zero :
    (∑ x ∈ Finset.range 55,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (201 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_201 :
    recurrence2Scalar3Shift.coeff 201 =
      (((9487645006180730288289484844646173634531704690001600035356656146 * 10 ^ 70 +
        0931451186914032277680733102854794740813176124859052337167936075713358) * 10 ^ 70 +
        4926701296148672822479682156571363961164891894366078455460488693632954) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 202 = 0 +
    202 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 106 = 32 +
      74 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 74 = 19 +
      55 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_201_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_202_suffix_zero :
    (∑ x ∈ Finset.range 56,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (202 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_202 :
    recurrence2Scalar3Shift.coeff 202 =
      -(((10023946297185480540696779100374905682559563603798964772294470262 * 10 ^ 70 +
        8409054120106950195847259850492012283478943619726253344905848798304526) * 10 ^ 70 +
        9939700007179196382207025303671886471716327775837940070509477028188114) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 203 = 0 +
    203 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 203 = 32 +
      171 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 171 = 32 +
      139 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 139 = 32 +
      107 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 19 +
      56 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_202_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_203_suffix_zero :
    (∑ x ∈ Finset.range 57,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (203 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_203 :
    recurrence2Scalar3Shift.coeff 203 =
      -(((10854721966917124371099952202004747848293724463227111385788756079 * 10 ^ 70 +
        6399284443177423959150805284968924112625938705597238497264196059016284) * 10 ^ 70 +
        9937752164713766242383252552674546887547825279281074504146923933774727) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 204 = 0 +
    204 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 204 = 32 +
      172 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 172 = 32 +
      140 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 140 = 32 +
      108 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 108 = 32 +
      76 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 76 = 19 +
      57 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_203_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_204_suffix_zero :
    (∑ x ∈ Finset.range 58,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (204 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_204 :
    recurrence2Scalar3Shift.coeff 204 =
      (((92205375865141031622757764176256380215466505642650518595994419112 * 10 ^ 70 +
        5990313135572008337819063357628995310797401611504979604140640547175441) * 10 ^ 70 +
        7847528021466155829607699744722238443536063291176012565599053471941763) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 205 = 0 +
    205 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 205 = 32 +
      173 by norm_num, Finset.sum_range_add]
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
    rw [show 77 = 19 +
      58 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_204_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_205_suffix_zero :
    (∑ x ∈ Finset.range 59,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (205 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_205 :
    recurrence2Scalar3Shift.coeff 205 =
      -(((297363908709561992311071468299749142435065467617972001871488079592 * 10 ^ 70 +
        3232498337217658202855565005782711203246674462571359336107631288926913) * 10 ^ 70 +
        5578831101013505778641841640505780330207424694789090942753204385384601) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 206 = 0 +
    206 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 206 = 32 +
      174 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 174 = 32 +
      142 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 142 = 32 +
      110 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 110 = 32 +
      78 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 78 = 19 +
      59 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_205_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_206_suffix_zero :
    (∑ x ∈ Finset.range 60,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (206 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_206 :
    recurrence2Scalar3Shift.coeff 206 =
      (((683814821093515261895514176483710997170679481820603442977823587188 * 10 ^ 70 +
        1174752001245505071034729071467057986708929997236490923120786384487084) * 10 ^ 70 +
        2286306145243708297990147425569052684909494236001094844537474206279059) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 207 = 0 +
    207 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 207 = 32 +
      175 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 175 = 32 +
      143 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 143 = 32 +
      111 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 19 +
      60 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_206_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_207_suffix_zero :
    (∑ x ∈ Finset.range 61,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (207 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_207 :
    recurrence2Scalar3Shift.coeff 207 =
      -(((1187354170957883417828269469523753687903944199155731742816935176611 * 10 ^ 70 +
        0969739881316593228797016063953496937703848614834559714480442564870475) * 10 ^ 70 +
        1026257813180107126868102531182532295357708163138428169548485609410123) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 208 = 0 +
    208 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 208 = 32 +
      176 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 176 = 32 +
      144 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 144 = 32 +
      112 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 112 = 32 +
      80 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 80 = 19 +
      61 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_207_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_208_suffix_zero :
    (∑ x ∈ Finset.range 62,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (208 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_208 :
    recurrence2Scalar3Shift.coeff 208 =
      (((1336861326723046781035244245718655317558539376069113954449099748623 * 10 ^ 70 +
        3216070652671004553851165586449262263029859872552372114299254693402556) * 10 ^ 70 +
        1278863960566170219695854868716203716390085950075076578993401617738389) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 209 = 0 +
    209 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 209 = 32 +
      177 by norm_num, Finset.sum_range_add]
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
    rw [show 81 = 19 +
      62 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_208_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_209_suffix_zero :
    (∑ x ∈ Finset.range 63,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (209 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_209 :
    recurrence2Scalar3Shift.coeff 209 =
      (((296236935032221739628149598306647218362031491484623673503949494047 * 10 ^ 70 +
        1227850666781853696941097697742245579103467142431679257709090011934623) * 10 ^ 70 +
        7626014820625877619936079188641401266175300193169453782945288670545383) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 210 = 0 +
    210 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 210 = 32 +
      178 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 178 = 32 +
      146 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 19 +
      63 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_209_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_210_suffix_zero :
    (∑ x ∈ Finset.range 64,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (210 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_210 :
    recurrence2Scalar3Shift.coeff 210 =
      -(((6958860517356519880978445361216015873740437308802430100351894588669 * 10 ^ 70 +
        3709511799973111218118434889290218799480102519083067221962187864092832) * 10 ^ 70 +
        1869474230287312139830825266023997210518837368812611326598310206862883) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 211 = 0 +
    211 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 211 = 32 +
      179 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 19 +
      64 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_210_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_211_suffix_zero :
    (∑ x ∈ Finset.range 65,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (211 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_211 :
    recurrence2Scalar3Shift.coeff 211 =
      (((24753911114979836431765086575832464934780892806378350940980731332095 * 10 ^ 70 +
        0579339331548262340198629434560319087445997890102274044814572631557309) * 10 ^ 70 +
        5060209694044071102518124896044708753042584627690933005017568720442707) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 212 = 0 +
    212 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 212 = 32 +
      180 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 180 = 32 +
      148 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 148 = 32 +
      116 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 116 = 32 +
      84 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 84 = 19 +
      65 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_211_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_212_suffix_zero :
    (∑ x ∈ Finset.range 66,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (212 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_212 :
    recurrence2Scalar3Shift.coeff 212 =
      -(((63350556360526446349376800990827123966219357856802819781910781162826 * 10 ^ 70 +
        3998166656180056358143554499133022819535284389459809551066873140528686) * 10 ^ 70 +
        5067874871528545213253943792452155175426565347068960078885701046029187) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 213 = 0 +
    213 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 213 = 32 +
      181 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 181 = 32 +
      149 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 149 = 32 +
      117 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 117 = 32 +
      85 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 85 = 19 +
      66 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_212_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_213_suffix_zero :
    (∑ x ∈ Finset.range 67,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (213 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_213 :
    recurrence2Scalar3Shift.coeff 213 =
      (((135284065247854226564862372685451241257520185711198147156071615378701 * 10 ^ 70 +
        0121207410430559769597921503918700865453418534940888582400295693384555) * 10 ^ 70 +
        1748403176009583835944224502377783796660977159648567228025414057511722) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 214 = 0 +
    214 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 214 = 32 +
      182 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 182 = 32 +
      150 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 19 +
      67 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_213_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_214_suffix_zero :
    (∑ x ∈ Finset.range 68,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (214 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_214 :
    recurrence2Scalar3Shift.coeff 214 =
      -(((252072991535807150458868974137229238934999124031373031153465582232373 * 10 ^ 70 +
        3800387688205079983984035597618712923444687303838643232056274909123663) * 10 ^ 70 +
        9701432102910678849383610126690671280968099377457216785833720931307021) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 215 = 0 +
    215 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 215 = 32 +
      183 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 19 +
      68 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_214_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_215_suffix_zero :
    (∑ x ∈ Finset.range 69,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (215 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_215 :
    recurrence2Scalar3Shift.coeff 215 =
      (((414860082638920230154661905892720919442272889026265555641249868465224 * 10 ^ 70 +
        2580652620020414121033494282626772788651774046062018689278733202129025) * 10 ^ 70 +
        1803874986324026154725090140915512959739625527176563204567496514267234) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 216 = 0 +
    216 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 216 = 32 +
      184 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 184 = 32 +
      152 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 152 = 32 +
      120 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 120 = 32 +
      88 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 88 = 19 +
      69 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_215_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_216_suffix_zero :
    (∑ x ∈ Finset.range 70,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (216 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_216 :
    recurrence2Scalar3Shift.coeff 216 =
      -(((597399795664008549129478140894280020528707275124652927406271642834597 * 10 ^ 70 +
        7273855692415566658116114367070359683853813431728495431704432454887122) * 10 ^ 70 +
        0346317715760224680807257959314944676436495467051925108686667476012827) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 217 = 0 +
    217 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 217 = 32 +
      185 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 185 = 32 +
      153 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 153 = 32 +
      121 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 121 = 32 +
      89 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 89 = 19 +
      70 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_216_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_217_suffix_zero :
    (∑ x ∈ Finset.range 71,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (217 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_217 :
    recurrence2Scalar3Shift.coeff 217 =
      (((720537547910563220747853104308554463313283333249673215583967100969400 * 10 ^ 70 +
        2944044702736351490154193729155511125412191844900095965928781534735562) * 10 ^ 70 +
        2991311460102604572534166448337420376189531875994764443932781482102043) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 218 = 0 +
    218 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 218 = 32 +
      186 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 186 = 32 +
      154 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 19 +
      71 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_217_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_218_suffix_zero :
    (∑ x ∈ Finset.range 72,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (218 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_218 :
    recurrence2Scalar3Shift.coeff 218 =
      -(((620281461112726492270832933792190727562429331611482856114027597283771 * 10 ^ 70 +
        7237749697745524779023473283816919459947822033656594718007908359086617) * 10 ^ 70 +
        7991798271178611214762382969749054128981144963563662277289869851580037) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 219 = 0 +
    219 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 219 = 32 +
      187 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 19 +
      72 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_218_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_219_suffix_zero :
    (∑ x ∈ Finset.range 73,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (219 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_219 :
    recurrence2Scalar3Shift.coeff 219 =
      (((16091955425207640520363956231000053621017886181065332781118944867561 * 10 ^ 70 +
        8212328423671394222768852138633284816216931062105207465479901078931428) * 10 ^ 70 +
        8616881117440930742488936238936081374559501387061907385791407231777621) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 220 = 0 +
    220 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 220 = 32 +
      188 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 188 = 32 +
      156 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 156 = 32 +
      124 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 124 = 32 +
      92 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 92 = 19 +
      73 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_219_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_220_suffix_zero :
    (∑ x ∈ Finset.range 74,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (220 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_220 :
    recurrence2Scalar3Shift.coeff 220 =
      (((1508791904422324361398127499892966062000001401665114593254333487707781 * 10 ^ 70 +
        1321396885979176512582029405885920903804984178259144806825697806998069) * 10 ^ 70 +
        7144332708006741786491164393669207171059623658786896469667151566508183) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 221 = 0 +
    221 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 221 = 32 +
      189 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 189 = 32 +
      157 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 157 = 32 +
      125 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 125 = 32 +
      93 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 93 = 19 +
      74 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_220_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_221_suffix_zero :
    (∑ x ∈ Finset.range 75,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (221 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_221 :
    recurrence2Scalar3Shift.coeff 221 =
      -(((4499173537103262881392456778372404745655765223310923980527121248732276 * 10 ^ 70 +
        4754126118426452287352483475005908354523685822807895929983506312127143) * 10 ^ 70 +
        6887938433088826835503150075880907184207020034467269749276599772361451) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 222 = 0 +
    222 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 222 = 32 +
      190 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 190 = 32 +
      158 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 158 = 32 +
      126 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 126 = 32 +
      94 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 94 = 19 +
      75 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_221_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_222_suffix_zero :
    (∑ x ∈ Finset.range 76,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (222 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_222 :
    recurrence2Scalar3Shift.coeff 222 =
      (((9575784208609970766677245038643471253870903574426245428952672966982374 * 10 ^ 70 +
        5984118818686828910486911484835290624880123980384102744507688071997829) * 10 ^ 70 +
        1531987854921404386292255955514931115495445772292586861180184944396752) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 223 = 0 +
    223 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 223 = 32 +
      191 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 19 +
      76 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_222_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_223_suffix_zero :
    (∑ x ∈ Finset.range 77,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (223 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_223 :
    recurrence2Scalar3Shift.coeff 223 =
      -((((1 * 10 ^ 70 +
        7328984251466669372985966453993878033490025948807864609046280005835621) * 10 ^ 70 +
        4689522813561785925882117957782354807399430169356024256090306818453176) * 10 ^ 70 +
        8897075503430078164684607997002893293879019873648547893033929788223856) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 224 = 0 +
    224 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 224 = 32 +
      192 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 192 = 32 +
      160 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 160 = 32 +
      128 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 128 = 32 +
      96 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 96 = 19 +
      77 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_223_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_224_suffix_zero :
    (∑ x ∈ Finset.range 78,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (224 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_224 :
    recurrence2Scalar3Shift.coeff 224 =
      ((((2 * 10 ^ 70 +
        8160968261405189527778019038577455785316673645575917300933446566011458) * 10 ^ 70 +
        0790224646127543034754079996689120919406620155066658707313733366237595) * 10 ^ 70 +
        8421083485591042237380224168750414788968778611512585684146410040529875) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 225 = 0 +
    225 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 225 = 32 +
      193 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 193 = 32 +
      161 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 161 = 32 +
      129 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 129 = 32 +
      97 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 97 = 19 +
      78 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_224_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_225_suffix_zero :
    (∑ x ∈ Finset.range 79,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (225 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_225 :
    recurrence2Scalar3Shift.coeff 225 =
      -((((4 * 10 ^ 70 +
        2097656306435229660098181783981883510505133885362229380335678753006579) * 10 ^ 70 +
        0440535723240870036489799771245283490875356242375466836258762467855447) * 10 ^ 70 +
        8793616332193458284649241943383345348369116287721583728808262666963518) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 226 = 0 +
    226 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 226 = 32 +
      194 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 194 = 32 +
      162 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 162 = 32 +
      130 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 130 = 32 +
      98 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 98 = 19 +
      79 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_225_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_226_suffix_zero :
    (∑ x ∈ Finset.range 80,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (226 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_226 :
    recurrence2Scalar3Shift.coeff 226 =
      ((((5 * 10 ^ 70 +
        8610909030200441716771388159824568000877643747081139493137267266558986) * 10 ^ 70 +
        8517887644652286479904480772033046109662350484132591654350077641225928) * 10 ^ 70 +
        6546181089456324016429579566308042327857829990761311584574824554713429) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 227 = 0 +
    227 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 227 = 32 +
      195 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 19 +
      80 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_226_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_227_suffix_zero :
    (∑ x ∈ Finset.range 81,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (227 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_227 :
    recurrence2Scalar3Shift.coeff 227 =
      -((((7 * 10 ^ 70 +
        6505177962071642768580298170613411729770790825546911366632432016940964) * 10 ^ 70 +
        5823485128736441184902386125544451057282217812232077799329214060977552) * 10 ^ 70 +
        6911863961525879770386126322357574440558974594000042484523749177114570) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 228 = 0 +
    228 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 228 = 32 +
      196 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 196 = 32 +
      164 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 164 = 32 +
      132 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 132 = 32 +
      100 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 100 = 19 +
      81 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_227_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_228_suffix_zero :
    (∑ x ∈ Finset.range 82,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (228 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_228 :
    recurrence2Scalar3Shift.coeff 228 =
      ((((9 * 10 ^ 70 +
        3922960816593053997552499453260996355099086174893055000335827898668625) * 10 ^ 70 +
        5673032164422917492031022757664932647295165378538138890288697981216336) * 10 ^ 70 +
        8509276177321234124194819178396789895170045373798976065558215535884837) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 229 = 0 +
    229 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 229 = 32 +
      197 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 197 = 32 +
      165 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 19 +
      82 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_228_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_229_suffix_zero :
    (∑ x ∈ Finset.range 83,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (229 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_229 :
    recurrence2Scalar3Shift.coeff 229 =
      -((((10 * 10 ^ 70 +
        8505889086560416513201815858687714734991611443895536313748773266574221) * 10 ^ 70 +
        9100689806662277673354349502581287253671053706978126779383677287807449) * 10 ^ 70 +
        1275575661368846164405260365162601312323380055704318925434417044353479) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 230 = 0 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 32 +
      102 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 102 = 19 +
      83 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_229_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_230_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (230 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (230 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_230_suffix_zero :
    (∑ x ∈ Finset.range 84,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (230 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_230 :
    recurrence2Scalar3Shift.coeff 230 =
      ((((11 * 10 ^ 70 +
        7713717355404766978385537460293410992866574132312995882504119879947453) * 10 ^ 70 +
        8312994183753055606763575676353225351582991311948337601588122282866466) * 10 ^ 70 +
        4443756915070275423609435132299358003536063149509043182491361277170037) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 231 = 1 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 32 +
      102 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 102 = 18 +
      84 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_230_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_230_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_231_prefix_zero :
    (∑ x ∈ Finset.range 2,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (231 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (231 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_231_suffix_zero :
    (∑ x ∈ Finset.range 85,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (231 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_231 :
    recurrence2Scalar3Shift.coeff 231 =
      -((((11 * 10 ^ 70 +
        9259268082698518545249092762584830995462594278846618980350570187329473) * 10 ^ 70 +
        6788824828340364822153731194052154833799219861256910009393922050124728) * 10 ^ 70 +
        9608415282249725633538417973596674338303308054030040382336475356470133) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 232 = 2 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 32 +
      102 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 102 = 17 +
      85 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_231_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_231_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_232_prefix_zero :
    (∑ x ∈ Finset.range 3,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (232 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (232 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_232_suffix_zero :
    (∑ x ∈ Finset.range 86,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (232 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_232 :
    recurrence2Scalar3Shift.coeff 232 =
      ((((11 * 10 ^ 70 +
        1576171684141322820159832351238650866755124263095193711341117276011912) * 10 ^ 70 +
        2960938385934977543479360951060892822580786001114744487107582000787394) * 10 ^ 70 +
        6542277173614285720360771661798252547451901490090564446990547597784911) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 233 = 3 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 32 +
      102 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 102 = 16 +
      86 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_232_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_232_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_233_prefix_zero :
    (∑ x ∈ Finset.range 4,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (233 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (233 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_233_suffix_zero :
    (∑ x ∈ Finset.range 87,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (233 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_233 :
    recurrence2Scalar3Shift.coeff 233 =
      -((((9 * 10 ^ 70 +
        4212235126228245450031901468774565670829302223816306995941757282593478) * 10 ^ 70 +
        0102067131984449302947552161114411232125625392636295221011616196993920) * 10 ^ 70 +
        3145769852712949075569074783894492917147406272657025068112862773351301) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 234 = 4 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 32 +
      102 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 102 = 15 +
      87 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_233_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_233_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
