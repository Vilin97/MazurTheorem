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

private theorem recurrence2Scalar3Shift_coeff_153_suffix_zero :
    (∑ x ∈ Finset.range 7,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (153 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_153 :
    recurrence2Scalar3Shift.coeff 153 =
      -(((81468665989986180789924249248377597031716 * 10 ^ 70 +
        2799768159874043811953837521923455826041668527564969344742161636063707) * 10 ^ 70 +
        6401210147125554272511196035712196032975840496412314253875995878574389) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 154 = 0 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 19 +
      7 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_153_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_154_suffix_zero :
    (∑ x ∈ Finset.range 8,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (154 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_154 :
    recurrence2Scalar3Shift.coeff 154 =
      -(((2835026430081224321770572766005771221995117 * 10 ^ 70 +
        7094006481550377611906127449648518547848747936916154613874216231036299) * 10 ^ 70 +
        0115358906609776109022630630506217797056885549942178988947155288634861) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 155 = 0 +
    155 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 32 +
      59 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 19 +
      8 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_154_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_155_suffix_zero :
    (∑ x ∈ Finset.range 9,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (155 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_155 :
    recurrence2Scalar3Shift.coeff 155 =
      (((11037303070979080906845240123516539586406024 * 10 ^ 70 +
        7114702803647535492544296846573833545072715558265095196925119539829767) * 10 ^ 70 +
        9031969067847684140005355204236379558399449042296931633457008325880960) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 156 = 0 +
    156 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 156 = 32 +
      124 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 124 = 32 +
      92 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 92 = 32 +
      60 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 60 = 32 +
      28 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 28 = 19 +
      9 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_155_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_156_suffix_zero :
    (∑ x ∈ Finset.range 10,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (156 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_156 :
    recurrence2Scalar3Shift.coeff 156 =
      -(((5501809289725788901402351403341080152109638 * 10 ^ 70 +
        6475730537204749330581551493595442418749471907004445601184486527012287) * 10 ^ 70 +
        4354220887822479273100460418282225317186361243403219094495664836584201) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 157 = 0 +
    157 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 157 = 32 +
      125 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 125 = 32 +
      93 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 93 = 32 +
      61 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 61 = 32 +
      29 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 29 = 19 +
      10 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_156_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_157_suffix_zero :
    (∑ x ∈ Finset.range 11,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (157 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_157 :
    recurrence2Scalar3Shift.coeff 157 =
      -(((111216042764848306251494588269297198495512035 * 10 ^ 70 +
        4756185320479037714321418044490016127203981810753470981151736457334417) * 10 ^ 70 +
        7004201785041072124111625679467201491472841911230786229464127658662396) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 158 = 0 +
    158 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 158 = 32 +
      126 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 126 = 32 +
      94 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 94 = 32 +
      62 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 62 = 32 +
      30 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 30 = 19 +
      11 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_157_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_158_suffix_zero :
    (∑ x ∈ Finset.range 12,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (158 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_158 :
    recurrence2Scalar3Shift.coeff 158 =
      (((469706903038386060014111285545528789069839490 * 10 ^ 70 +
        3373250401181582370904267236366199861810849874028790894647168294659174) * 10 ^ 70 +
        3713865163618447121974224948814823199716831319408742118906446285698240) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 159 = 0 +
    159 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 19 +
      12 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_158_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_159_suffix_zero :
    (∑ x ∈ Finset.range 13,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (159 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_159 :
    recurrence2Scalar3Shift.coeff 159 =
      -(((435863946780772822697541453296721087005319778 * 10 ^ 70 +
        6837793689141999683587709053565233259671281592372943982055127640478848) * 10 ^ 70 +
        0870745965112288401190804289871867774007884167408862256296826847933018) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 160 = 0 +
    160 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 160 = 32 +
      128 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 128 = 32 +
      96 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 19 +
      13 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_159_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_160_suffix_zero :
    (∑ x ∈ Finset.range 14,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (160 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_160 :
    recurrence2Scalar3Shift.coeff 160 =
      -(((3753665361542200877432072687325691884871835834 * 10 ^ 70 +
        9633275277520679915237431481775325844024955304882846468337146734384430) * 10 ^ 70 +
        8273720267245717234980710970889374209367551997414611072251372009854227) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 161 = 0 +
    161 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 161 = 32 +
      129 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 129 = 32 +
      97 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 97 = 32 +
      65 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 65 = 32 +
      33 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 33 = 19 +
      14 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_160_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_161_suffix_zero :
    (∑ x ∈ Finset.range 15,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (161 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_161 :
    recurrence2Scalar3Shift.coeff 161 =
      (((18884001503145949894152753339905778337792255948 * 10 ^ 70 +
        1563755453696311757265186589732057612918510443538097375293318575908971) * 10 ^ 70 +
        5609228984272285313313297225485906996309870201182345628704695677233300) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 162 = 0 +
    162 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 162 = 32 +
      130 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 130 = 32 +
      98 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 98 = 32 +
      66 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 66 = 32 +
      34 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 34 = 19 +
      15 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_161_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_162_suffix_zero :
    (∑ x ∈ Finset.range 16,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (162 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_162 :
    recurrence2Scalar3Shift.coeff 162 =
      -(((29263874371678269989523141818626184191602663596 * 10 ^ 70 +
        9761509737605323189296151501092569456662347972405333981012840833515180) * 10 ^ 70 +
        2291618513893013258763855069848681521912069636275770312636682649632580) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 163 = 0 +
    163 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 19 +
      16 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_162_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_163_suffix_zero :
    (∑ x ∈ Finset.range 17,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (163 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_163 :
    recurrence2Scalar3Shift.coeff 163 =
      -(((94628295077454830002402421557398044291585547047 * 10 ^ 70 +
        7738875885647185258973475126294835370521275035469593711219835965574468) * 10 ^ 70 +
        3578269855448502697050561481857766757238341029971304534942772765383998) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 164 = 0 +
    164 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 68 = 32 +
      36 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 36 = 19 +
      17 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_163_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_164_suffix_zero :
    (∑ x ∈ Finset.range 18,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (164 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_164 :
    recurrence2Scalar3Shift.coeff 164 =
      (((667555444138041952920227930804366208259480391479 * 10 ^ 70 +
        0461369448923307457787473337847682565232924087557450584815633727095908) * 10 ^ 70 +
        0659434666460671234938417895961080364503447890319659998758113749678773) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 165 = 0 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 19 +
      18 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_164_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_165_suffix_zero :
    (∑ x ∈ Finset.range 19,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (165 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_165 :
    recurrence2Scalar3Shift.coeff 165 =
      -(((1534100728704687048577128870792623412285660685729 * 10 ^ 70 +
        3571004664345008131212153661468834082063615624676257108836586719357985) * 10 ^ 70 +
        1042002937887938941760993702376438939150277335796095499586298879192785) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 166 = 0 +
    166 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 70 = 32 +
      38 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 38 = 19 +
      19 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_165_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_166_suffix_zero :
    (∑ x ∈ Finset.range 20,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (166 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_166 :
    recurrence2Scalar3Shift.coeff 166 =
      -(((1019163377748713692323801689410221105747799086347 * 10 ^ 70 +
        2470226184918275207792471993222450109959685586529999345859474649342375) * 10 ^ 70 +
        4399251623102571350799650012758413148714257226095408052478430038018200) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 167 = 0 +
    167 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 71 = 32 +
      39 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 39 = 19 +
      20 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_166_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_167_suffix_zero :
    (∑ x ∈ Finset.range 21,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (167 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_167 :
    recurrence2Scalar3Shift.coeff 167 =
      (((19198142209700721453202714787710054988361840200748 * 10 ^ 70 +
        4782786442432929497198878994918084072186055472000623800007987693539874) * 10 ^ 70 +
        7675723922045585223808495998311987094224720168058110158017741679898111) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 168 = 0 +
    168 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 72 = 32 +
      40 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 40 = 19 +
      21 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_167_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_168_suffix_zero :
    (∑ x ∈ Finset.range 22,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (168 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_168 :
    recurrence2Scalar3Shift.coeff 168 =
      -(((62509562219346061999946335553332450872564828592735 * 10 ^ 70 +
        1310542975392122557909807391813969717131978676335732338098416256975648) * 10 ^ 70 +
        2098540903868206692613685437205522071332531519858950584521704826948323) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 169 = 0 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 73 = 32 +
      41 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 41 = 19 +
      22 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_168_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_169_suffix_zero :
    (∑ x ∈ Finset.range 23,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (169 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_169 :
    recurrence2Scalar3Shift.coeff 169 =
      (((51258227449741461269345056800482866055362498364027 * 10 ^ 70 +
        9756908339063560387627929101773883000481981107047097084014758216662484) * 10 ^ 70 +
        1189663774330818373104883894447463555976953318462384484930698564451755) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 170 = 0 +
    170 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 74 = 32 +
      42 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 42 = 19 +
      23 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_169_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_170_suffix_zero :
    (∑ x ∈ Finset.range 24,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (170 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_170 :
    recurrence2Scalar3Shift.coeff 170 =
      (((396868486930722952016739359318772818029339992006424 * 10 ^ 70 +
        3767313499249938486150156811349075491942771871853856214125436655927327) * 10 ^ 70 +
        1856399822448679625846804954607371730940042634628794137386433897322489) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 171 = 0 +
    171 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 75 = 32 +
      43 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 43 = 19 +
      24 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_170_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_171_suffix_zero :
    (∑ x ∈ Finset.range 25,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (171 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_171 :
    recurrence2Scalar3Shift.coeff 171 =
      -(((1972380266312303808040372254996075872057649975288913 * 10 ^ 70 +
        8279512727623031775812043019703243984087626318816008762159581493242095) * 10 ^ 70 +
        2881184469292085763012915134504412233575727391147766951333071809965448) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 172 = 0 +
    172 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 76 = 32 +
      44 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 44 = 19 +
      25 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_171_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_172_suffix_zero :
    (∑ x ∈ Finset.range 26,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (172 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_172 :
    recurrence2Scalar3Shift.coeff 172 =
      (((3823713938391227624828659223104384706987246525294173 * 10 ^ 70 +
        2345631493101963856564144002513184347620468719420608513374847294909432) * 10 ^ 70 +
        7450654530414869734920106862526178978951102874574204812256796057532242) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 173 = 0 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 77 = 32 +
      45 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 45 = 19 +
      26 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_172_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_173_suffix_zero :
    (∑ x ∈ Finset.range 27,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (173 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_173 :
    recurrence2Scalar3Shift.coeff 173 =
      (((3239554824422180330814584093541087180693180147759368 * 10 ^ 70 +
        0723306323158250300868784001924426645086193076247720214190414100258706) * 10 ^ 70 +
        9242080433852004292497986837258087837793961361314992227222216863887308) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 174 = 0 +
    174 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 78 = 32 +
      46 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 46 = 19 +
      27 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_173_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_174_suffix_zero :
    (∑ x ∈ Finset.range 28,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (174 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_174 :
    recurrence2Scalar3Shift.coeff 174 =
      -(((45909923651969754591361804072824035614930661998783657 * 10 ^ 70 +
        4559494488891595777202312985004575941509437925594218990717352891692167) * 10 ^ 70 +
        6068525264300682372211060630034254027642010209872054762524249826887321) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 175 = 0 +
    175 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 79 = 32 +
      47 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 47 = 19 +
      28 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_174_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_175_suffix_zero :
    (∑ x ∈ Finset.range 29,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (175 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_175 :
    recurrence2Scalar3Shift.coeff 175 =
      (((145405735663449747561410513627340145936968553481957609 * 10 ^ 70 +
        9856946805635743651131990939705351144558092258951553526622469639287183) * 10 ^ 70 +
        2664792800786697295929539963378203495708944065048879320726158434108878) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 176 = 0 +
    176 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 80 = 32 +
      48 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 48 = 19 +
      29 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_175_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_176_suffix_zero :
    (∑ x ∈ Finset.range 30,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (176 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_176 :
    recurrence2Scalar3Shift.coeff 176 =
      -(((158726805548970846304583953876377062230735366816289685 * 10 ^ 70 +
        1654679587573347802353302302879107079587680919093719494517175645950700) * 10 ^ 70 +
        9887527904546268851726714798539826445913155739258837150096439064868450) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 177 = 0 +
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
    rw [show 49 = 19 +
      30 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_176_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_177_suffix_zero :
    (∑ x ∈ Finset.range 31,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (177 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_177 :
    recurrence2Scalar3Shift.coeff 177 =
      -(((618148691879452430885130700434081241798720674004037918 * 10 ^ 70 +
        5490889947059363719834917490365311008024298939501919992835417759741218) * 10 ^ 70 +
        2246582924308845689259614030681123696947491546160533471937598709571792) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 178 = 0 +
    178 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 19 +
      31 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_177_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_178_suffix_zero :
    (∑ x ∈ Finset.range 32,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (178 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_178 :
    recurrence2Scalar3Shift.coeff 178 =
      (((3654722310154998627780558037856579391812275172431806874 * 10 ^ 70 +
        4015317207121611043147136718973716745637151122120759609902680647783817) * 10 ^ 70 +
        9375470739222101517155409072662631012201833926256938844248969072616283) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 179 = 0 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 19 +
      32 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_178_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_179_suffix_zero :
    (∑ x ∈ Finset.range 33,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (179 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_179 :
    recurrence2Scalar3Shift.coeff 179 =
      -(((8870827724221676230746220724002389467148180252886259493 * 10 ^ 70 +
        9420160660235692567994262936548842815542975792517594394771245898925495) * 10 ^ 70 +
        9779098771393554148969791941534771170389350655669742814427024928249895) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 180 = 0 +
    180 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 84 = 32 +
      52 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 52 = 19 +
      33 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_179_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_180_suffix_zero :
    (∑ x ∈ Finset.range 34,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (180 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_180 :
    recurrence2Scalar3Shift.coeff 180 =
      (((4594842227086738595751684934659831327881519748065526687 * 10 ^ 70 +
        5590461841658212555576395867755798192240255014051499319164965488733962) * 10 ^ 70 +
        9925283906743670701504123628159114257813959850699441086807398499099867) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 181 = 0 +
    181 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 19 +
      34 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_180_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_181_suffix_zero :
    (∑ x ∈ Finset.range 35,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (181 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_181 :
    recurrence2Scalar3Shift.coeff 181 =
      (((52068144627096211807581271952658750268713950814159434442 * 10 ^ 70 +
        6277505697154912504173046137190637665366527382443183718069991588643994) * 10 ^ 70 +
        9965516006291887463487872816650972992689232977128058784578285264926899) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 182 = 0 +
    182 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 19 +
      35 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_181_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_182_suffix_zero :
    (∑ x ∈ Finset.range 36,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (182 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_182 :
    recurrence2Scalar3Shift.coeff 182 =
      -(((234026634952173438830290046925778115085568404659995918693 * 10 ^ 70 +
        0192436322438757415130905725241741057789296159697711300532886907754337) * 10 ^ 70 +
        4296024215889431454286050230906343173213742758663976237343828224310323) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 183 = 0 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 19 +
      36 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_182_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_183_suffix_zero :
    (∑ x ∈ Finset.range 37,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (183 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_183 :
    recurrence2Scalar3Shift.coeff 183 =
      (((499195232997513314012764576349976584442088063926758164792 * 10 ^ 70 +
        4702288302326583629180391112873760096424629141168779866116770937214296) * 10 ^ 70 +
        5694033893318328806993034002227852883148521728287018249101554752784191) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 184 = 0 +
    184 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 88 = 32 +
      56 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 56 = 19 +
      37 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_183_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_184_suffix_zero :
    (∑ x ∈ Finset.range 38,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (184 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_184 :
    recurrence2Scalar3Shift.coeff 184 =
      -(((166248006315937458013710974539351212109309417276016802330 * 10 ^ 70 +
        9553769675753775899819321718928956977694759305324554364924088382918768) * 10 ^ 70 +
        9935148805692368647974229535123304570755606065262728959893245073777573) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 185 = 0 +
    185 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 19 +
      38 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_184_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_185_suffix_zero :
    (∑ x ∈ Finset.range 39,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (185 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_185 :
    recurrence2Scalar3Shift.coeff 185 =
      -(((3013041961112276637661986517848484160008517496583087421007 * 10 ^ 70 +
        1058120493161501490769033176667418681162654750675502708496436851986403) * 10 ^ 70 +
        6171527315251892706567098158633203958588638775834651719962251484197940) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 186 = 0 +
    186 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 19 +
      39 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_185_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_186_suffix_zero :
    (∑ x ∈ Finset.range 40,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (186 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_186 :
    recurrence2Scalar3Shift.coeff 186 =
      (((12722761279915026636329494917699421546909032678651095583270 * 10 ^ 70 +
        2376912818099386379679004696454387487370053251546572499078246287132345) * 10 ^ 70 +
        9035215969503296314884095487563846081178172326839946699848286366485795) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 187 = 0 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 91 = 32 +
      59 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 59 = 19 +
      40 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_186_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_187_suffix_zero :
    (∑ x ∈ Finset.range 41,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (187 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_187 :
    recurrence2Scalar3Shift.coeff 187 =
      -(((27461863230088454769476340528496363907248749826602648481254 * 10 ^ 70 +
        6700361414785445749512694940889595956919800564823761409328047036467506) * 10 ^ 70 +
        6288014690920514527480501452526336806521970252262502682193895932505406) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 188 = 0 +
    188 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 92 = 32 +
      60 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 60 = 19 +
      41 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_187_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_188_suffix_zero :
    (∑ x ∈ Finset.range 42,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (188 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_188 :
    recurrence2Scalar3Shift.coeff 188 =
      (((17074540913738883852474944537469798915104704744300025015574 * 10 ^ 70 +
        5220180598950547115469077493376955177843441708344151823760591457698305) * 10 ^ 70 +
        0046267176506205510951380608357965893019468966474384969593985062282095) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 189 = 0 +
    189 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 93 = 32 +
      61 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 61 = 19 +
      42 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_188_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_189_suffix_zero :
    (∑ x ∈ Finset.range 43,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (189 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_189 :
    recurrence2Scalar3Shift.coeff 189 =
      (((121348441059211346575064884991976308049126703828981565968676 * 10 ^ 70 +
        1111092012402808910553832914188340626954524626702422964777339159919202) * 10 ^ 70 +
        1506464856601432186460881971143515298339081322985848402127927184927633) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 190 = 0 +
    190 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 94 = 32 +
      62 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 62 = 19 +
      43 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_189_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_190_suffix_zero :
    (∑ x ∈ Finset.range 44,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (190 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_190 :
    recurrence2Scalar3Shift.coeff 190 =
      -(((579207715759652673330394565298674457458689793763025232881828 * 10 ^ 70 +
        4380039350392152229107683394633530125940133992156632508983544632677375) * 10 ^ 70 +
        5913414291538946378203359518773022570257448300982073879832602181076101) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 191 = 0 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 19 +
      44 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_190_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_191_suffix_zero :
    (∑ x ∈ Finset.range 45,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (191 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_191 :
    recurrence2Scalar3Shift.coeff 191 =
      (((1425253554506197002289548736801505487527698755846217978396859 * 10 ^ 70 +
        3634234056722963998762257973704823213326459400973023857325791214541475) * 10 ^ 70 +
        5020870750823737363856501878415107176688363535661553467636072862041066) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 192 = 0 +
    192 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 19 +
      45 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_191_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_192_suffix_zero :
    (∑ x ∈ Finset.range 46,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (192 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_192 :
    recurrence2Scalar3Shift.coeff 192 =
      -(((1737672259765204840266102165903303807118096759173493644733856 * 10 ^ 70 +
        7951415668180214161277530471987905004965101646619695208872988237708610) * 10 ^ 70 +
        5954025712118473542193533091477959056252573135651308877574364453962814) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 193 = 0 +
    193 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 97 = 32 +
      65 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 65 = 19 +
      46 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_192_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_193_suffix_zero :
    (∑ x ∈ Finset.range 47,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (193 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_193 :
    recurrence2Scalar3Shift.coeff 193 =
      -(((2341213264667649007432497334380806019915742198671486700744085 * 10 ^ 70 +
        1583733026427652210261387153516457221071705028264831894975995607254881) * 10 ^ 70 +
        7672014356697147754300282264022145207441739717780744625844064254730728) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 194 = 0 +
    194 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 98 = 32 +
      66 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 66 = 19 +
      47 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_193_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
