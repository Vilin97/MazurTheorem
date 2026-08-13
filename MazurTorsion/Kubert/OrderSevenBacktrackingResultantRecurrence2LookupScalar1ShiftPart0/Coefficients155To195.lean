/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB0
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB5A6
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar1ShiftPart0Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: Scalar1Shift coefficient convolution

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

private theorem recurrence2Scalar1Shift_coeff_155_suffix_zero :
    (∑ x ∈ Finset.range 1,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (155 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_155 :
    recurrence2Scalar1Shift.coeff 155 =
      (((886990317553417365340326079102889722403428 * 10 ^ 70 +
        3485513170805482829383718500811227782583837647602068159557611407961313) * 10 ^ 70 +
        9746948229228646903379519017499391097463814372271744651759034996648256) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 28 = 27 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_155_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_156_suffix_zero :
    (∑ x ∈ Finset.range 2,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (156 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_156 :
    recurrence2Scalar1Shift.coeff 156 =
      -(((15589233748526093483384983207191922098328156 * 10 ^ 70 +
        5708571628820793838816359674699388235869143283408155421914178470654048) * 10 ^ 70 +
        7150921329751549208758476748056447720093267160829452762878677154122916) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 29 = 27 +
      2 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_156_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_157_suffix_zero :
    (∑ x ∈ Finset.range 3,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (157 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_157 :
    recurrence2Scalar1Shift.coeff 157 =
      (((46035707375859882669916432932738522719530436 * 10 ^ 70 +
        0637967144010813619688789538574251069856774376904761682387096166265195) * 10 ^ 70 +
        4168912328324689267755949356246875490830012531705787540191060161981510) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 30 = 27 +
      3 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_157_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_158_suffix_zero :
    (∑ x ∈ Finset.range 4,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (158 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_158 :
    recurrence2Scalar1Shift.coeff 158 =
      (((22142169091010871485334738454193585926296238 * 10 ^ 70 +
        2219688386379161470278184870833406279253271398417126564030872076589017) * 10 ^ 70 +
        8421163027996693527948456285724873017089903141807235234861574292409715) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 31 = 27 +
      4 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_158_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_159_suffix_zero :
    (∑ x ∈ Finset.range 5,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (159 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_159 :
    recurrence2Scalar1Shift.coeff 159 =
      -(((643971369409455896330066124950108607547529957 * 10 ^ 70 +
        0894768667670536250354892665249617330848416627395238399105742607021685) * 10 ^ 70 +
        3065743290741230023606071315851630599260570087779889016085783601122585) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 32 = 27 +
      5 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_159_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_160_suffix_zero :
    (∑ x ∈ Finset.range 6,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (160 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_160 :
    recurrence2Scalar1Shift.coeff 160 =
      (((2165128139851453263258489515387902443626227674 * 10 ^ 70 +
        8226606513746886640158950077652087356685053935819247288336468132734645) * 10 ^ 70 +
        3694212365322063615513111711717695609740862707724196901959461706539643) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 33 = 27 +
      6 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_160_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_161_suffix_zero :
    (∑ x ∈ Finset.range 7,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (161 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_161 :
    recurrence2Scalar1Shift.coeff 161 =
      -(((650679071797269329048492666663346648169868271 * 10 ^ 70 +
        5022273739802654957140349008538401138870643215876576054950678657575686) * 10 ^ 70 +
        2160092452312739890276676765372447293689579135156959648889139774428334) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 34 = 27 +
      7 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_161_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_162_suffix_zero :
    (∑ x ∈ Finset.range 8,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (162 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_162 :
    recurrence2Scalar1Shift.coeff 162 =
      -(((22443834002416588365733528769099420790632531145 * 10 ^ 70 +
        8650331387975975921256988342030588138863835674345251885987705369679168) * 10 ^ 70 +
        3408447547350557155642381683221493769736025968624605473433280173499464) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 35 = 27 +
      8 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_162_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_163_suffix_zero :
    (∑ x ∈ Finset.range 9,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (163 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_163 :
    recurrence2Scalar1Shift.coeff 163 =
      (((92966824065307781179311106749323414578710709034 * 10 ^ 70 +
        1361342290698882740817668388773051990831221314780292975027582414957842) * 10 ^ 70 +
        0389637717920891936754818888465104653393357847231393261608484244992826) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 36 = 27 +
      9 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_163_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_164_suffix_zero :
    (∑ x ∈ Finset.range 10,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (164 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_164 :
    recurrence2Scalar1Shift.coeff 164 =
      -(((107265744927887245643085483391415581528376730975 * 10 ^ 70 +
        5776559872929034693267768841346809556359478575515905349456207064771812) * 10 ^ 70 +
        2552242541112383168874399057251587976743586025385111497252973149425373) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 37 = 27 +
      10 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_164_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_165_suffix_zero :
    (∑ x ∈ Finset.range 11,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (165 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_165 :
    recurrence2Scalar1Shift.coeff 165 =
      -(((595390139376457092622470288088090112606515832448 * 10 ^ 70 +
        3700422056781712566571822460780346403107054975034754679617793318744000) * 10 ^ 70 +
        3040437469053315151807872720261734542224659567954618281780466238255289) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 38 = 27 +
      11 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_165_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_166_suffix_zero :
    (∑ x ∈ Finset.range 12,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (166 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_166 :
    recurrence2Scalar1Shift.coeff 166 =
      (((3408538964072156855035266622309015045699736104321 * 10 ^ 70 +
        7422604290556580941672506932892931845457534030951683595437264469293846) * 10 ^ 70 +
        0792951726801970509422991721749105936064950190299262749625455830675790) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 39 = 27 +
      12 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_166_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_167_suffix_zero :
    (∑ x ∈ Finset.range 13,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (167 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_167 :
    recurrence2Scalar1Shift.coeff 167 =
      -(((6818367262245516794490646341963396705315205707592 * 10 ^ 70 +
        2328765185461233969237544821236960809644855695188247797727256334614229) * 10 ^ 70 +
        3051415112596258469219564419315752127152036220392312220392025159336483) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 40 = 27 +
      13 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_167_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_168_suffix_zero :
    (∑ x ∈ Finset.range 14,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (168 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_168 :
    recurrence2Scalar1Shift.coeff 168 =
      -(((8721694667701095384220789250434751279410308153540 * 10 ^ 70 +
        9103626826504303600050621763148309236020291543107810877106461623640959) * 10 ^ 70 +
        0584685756606733100626037783267702170301615537979152827084876403579107) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 41 = 27 +
      14 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_168_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_169_suffix_zero :
    (∑ x ∈ Finset.range 15,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (169 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_169 :
    recurrence2Scalar1Shift.coeff 169 =
      (((101302537739292624382549817470854261424589063728256 * 10 ^ 70 +
        3026280211785199165039709850688360249977022156227983805148693765384003) * 10 ^ 70 +
        2665117994370880927014836478895190637833152780835067842334037376407289) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 42 = 27 +
      15 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_169_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_170_suffix_zero :
    (∑ x ∈ Finset.range 16,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (170 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_170 :
    recurrence2Scalar1Shift.coeff 170 =
      -(((299663067914350216652652164772621190020576859293972 * 10 ^ 70 +
        5915012580357120376026767934454604342964136094788774005900943545129370) * 10 ^ 70 +
        2951802167853971985771761642950059265397862578738251426072916122886023) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 43 = 27 +
      16 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_170_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_171_suffix_zero :
    (∑ x ∈ Finset.range 17,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (171 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_171 :
    recurrence2Scalar1Shift.coeff 171 =
      (((162450252686980207943927544314498158687340659294593 * 10 ^ 70 +
        2042390058601247454184189966776767204803592706619068713980715464276266) * 10 ^ 70 +
        6326614696784288194990264012983758008744881499301102243796765016897333) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 44 = 27 +
      17 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_171_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_172_suffix_zero :
    (∑ x ∈ Finset.range 18,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (172 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_172 :
    recurrence2Scalar1Shift.coeff 172 =
      (((2222911371892065603072569784132997867103495564678483 * 10 ^ 70 +
        8649287343806419534137023856411804462867859823890967058836965713425336) * 10 ^ 70 +
        8726826765568955743940913827088057878207358745920887614684855888903775) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 45 = 27 +
      18 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_172_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_173_suffix_zero :
    (∑ x ∈ Finset.range 19,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (173 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_173 :
    recurrence2Scalar1Shift.coeff 173 =
      -(((9966025575126411306127249015743202195334459432331672 * 10 ^ 70 +
        6659996040044604391058256506180242544271289192257101456831088143535012) * 10 ^ 70 +
        4765990002343919153334918227472719495351565181159354650593522679807506) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 46 = 27 +
      19 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_173_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_174_suffix_zero :
    (∑ x ∈ Finset.range 20,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (174 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_174 :
    recurrence2Scalar1Shift.coeff 174 =
      (((17522568292879007538200552479607370064976768901887472 * 10 ^ 70 +
        9703037494043086982087682134652513204889457810641266467462972221109338) * 10 ^ 70 +
        1277926594706573743367595540178258945209189901738397774556649630613578) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 47 = 27 +
      20 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_174_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_175_suffix_zero :
    (∑ x ∈ Finset.range 21,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (175 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_175 :
    recurrence2Scalar1Shift.coeff 175 =
      (((23254174632860596998677397422312270023969201491066283 * 10 ^ 70 +
        7232081913394119576415135254998810403405486327926016474260991094163774) * 10 ^ 70 +
        0147734555375448601917591422684886648106348589272390420835881810990180) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 48 = 27 +
      21 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_175_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_176_suffix_zero :
    (∑ x ∈ Finset.range 22,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (176 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_176 :
    recurrence2Scalar1Shift.coeff 176 =
      -(((244417521471003856794668660391864250623052224745442118 * 10 ^ 70 +
        6433613145686400300965183653529668750974003624299918494579889575587005) * 10 ^ 70 +
        4704478405535367333089205187627604922273835742682783310853511734736507) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 49 = 27 +
      22 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_176_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_177_suffix_zero :
    (∑ x ∈ Finset.range 23,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (177 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_177 :
    recurrence2Scalar1Shift.coeff 177 =
      (((730096202504125109500039931198630331738715154809541574 * 10 ^ 70 +
        0981293343686701860489605759970066679157588728706842957962635144398937) * 10 ^ 70 +
        6934763067661306000745934901245217796035177665544783512666743199148866) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 50 = 27 +
      23 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_177_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_178_suffix_zero :
    (∑ x ∈ Finset.range 24,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (178 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_178 :
    recurrence2Scalar1Shift.coeff 178 =
      -(((689047925274101235986807919681218976984317505616616929 * 10 ^ 70 +
        2736136317679568064823389884762013033764408410398805709367134693642241) * 10 ^ 70 +
        4869911018199551728931062552206446777677619462295430432245256947644880) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 51 = 27 +
      24 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_178_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_179_suffix_zero :
    (∑ x ∈ Finset.range 25,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (179 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_179 :
    recurrence2Scalar1Shift.coeff 179 =
      -(((3542015753836774697872379745616527055894824561699532524 * 10 ^ 70 +
        6095624584582239732701047820507081861989314217108365661255988565802267) * 10 ^ 70 +
        9881975241911630091103888945652844986100214361727620813863658874571772) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 52 = 27 +
      25 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_179_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_180_suffix_zero :
    (∑ x ∈ Finset.range 26,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (180 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_180 :
    recurrence2Scalar1Shift.coeff 180 =
      (((19325463630617371959333399248976476920740068489848893431 * 10 ^ 70 +
        7950283123339859186490031261273683055200452213757260501217172823997829) * 10 ^ 70 +
        6266246425443289373696608452873683235013426594388144189242420749613362) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 53 = 27 +
      26 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_180_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_181_suffix_zero :
    (∑ x ∈ Finset.range 27,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (181 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_181 :
    recurrence2Scalar1Shift.coeff 181 =
      -(((45228107552762663801464364949041145771895846327899268599 * 10 ^ 70 +
        3404242711265237345910440217271020079079184963701097825386407121403688) * 10 ^ 70 +
        0876887129545566477267623389627992871165807554388944287472649393439795) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 54 = 27 +
      27 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_181_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_182_suffix_zero :
    (∑ x ∈ Finset.range 28,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (182 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_182 :
    recurrence2Scalar1Shift.coeff 182 =
      (((18369247115629740771448706357053355300507692609690198483 * 10 ^ 70 +
        2362322293220202338000585317763331478778393262823970562828296322538481) * 10 ^ 70 +
        6205796117623520960641510615047796623945532745411494245621662709518791) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 55 = 27 +
      28 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_182_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_183_suffix_zero :
    (∑ x ∈ Finset.range 29,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (183 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_183 :
    recurrence2Scalar1Shift.coeff 183 =
      (((287070405650256075524028624462515387071640866001167456095 * 10 ^ 70 +
        1031875006655385405987313140698559875265762167883998257789250859568252) * 10 ^ 70 +
        3641302611556971292687877168782970367421879128372665732269814985536062) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 56 = 27 +
      29 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_183_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_184_suffix_zero :
    (∑ x ∈ Finset.range 30,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (184 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_184 :
    recurrence2Scalar1Shift.coeff 184 =
      -(((1248535514815045415873730304655401378247579246719579887476 * 10 ^ 70 +
        4402331141029558345248413486971598988108871021261638448479151828118510) * 10 ^ 70 +
        9283261462112197257364686968226890712452953998451951958078313050342988) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 57 = 27 +
      30 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_184_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_185_suffix_zero :
    (∑ x ∈ Finset.range 31,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (185 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_185 :
    recurrence2Scalar1Shift.coeff 185 =
      (((2619658967681088626413067703807365021715565823520796596586 * 10 ^ 70 +
        6640019964646903054591005689908965481765974539977122610302915602048155) * 10 ^ 70 +
        8248040871302298419259777965460179893035594514816865736761039189785275) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 58 = 27 +
      31 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_185_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_186_suffix_zero :
    (∑ x ∈ Finset.range 32,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (186 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_186 :
    recurrence2Scalar1Shift.coeff 186 =
      -(((733088739895802789571914975576636029993789130110767093722 * 10 ^ 70 +
        7214407055246195757507090732586113640775643720045854479843180784888860) * 10 ^ 70 +
        7085118892945211924081806379656431372957647949748528241487417521134851) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 59 = 27 +
      32 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_186_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_187_suffix_zero :
    (∑ x ∈ Finset.range 33,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (187 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_187 :
    recurrence2Scalar1Shift.coeff 187 =
      -(((16486739110796690907529953639944623675363714388008670313250 * 10 ^ 70 +
        6476168228901685633304805389820606059500424339235074365556884942819799) * 10 ^ 70 +
        3966514110117851218800970432705412594611933830317449434877478524916265) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 60 = 27 +
      33 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_187_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_188_suffix_zero :
    (∑ x ∈ Finset.range 34,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (188 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_188 :
    recurrence2Scalar1Shift.coeff 188 =
      (((68953939978707725027454586553831417213123980218509373452113 * 10 ^ 70 +
        6908156328905351408455517156691353027127625470655388155364772152501043) * 10 ^ 70 +
        8724802090137977457755557579202500029026718542830170979742669800674183) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 61 = 27 +
      34 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_188_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_189_suffix_zero :
    (∑ x ∈ Finset.range 35,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (189 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_189 :
    recurrence2Scalar1Shift.coeff 189 =
      -(((148967641967146029332960418902349729952487550714191899400371 * 10 ^ 70 +
        0268936681769637640699078007065769941638534074786201218947726364189983) * 10 ^ 70 +
        1599498440873521210377373982681674431027804994683460578722828861247302) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 62 = 27 +
      35 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_189_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_190_suffix_zero :
    (∑ x ∈ Finset.range 36,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (190 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_190 :
    recurrence2Scalar1Shift.coeff 190 =
      (((93481402046024998103014500112789593557513043560734649027125 * 10 ^ 70 +
        8797867870554273055640041181256373783582301806103995513252953749580576) * 10 ^ 70 +
        5028296307112103500513097542193962342300868408314767430196116640807129) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 63 = 27 +
      36 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_190_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_191_suffix_zero :
    (∑ x ∈ Finset.range 37,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (191 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_191 :
    recurrence2Scalar1Shift.coeff 191 =
      (((661639847450109389544831642019700294110262714922003050769282 * 10 ^ 70 +
        2006986271952568010784547146418615134343518035917365500321095576434492) * 10 ^ 70 +
        7847538875675949803859509146056172332222835537847801165773799589165066) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 64 = 27 +
      37 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_191_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_192_suffix_zero :
    (∑ x ∈ Finset.range 38,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (192 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_192 :
    recurrence2Scalar1Shift.coeff 192 =
      -(((3188266108726376662244641539538236906147243699915858577715991 * 10 ^ 70 +
        7618948272065439064720063515370086525152180547726494962637725647528657) * 10 ^ 70 +
        2906431859299969800387468369040903333314249835707711302769896054661075) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 65 = 27 +
      38 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_192_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_193_suffix_zero :
    (∑ x ∈ Finset.range 39,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (193 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_193 :
    recurrence2Scalar1Shift.coeff 193 =
      (((7946277162688838449529748463371949961076455189598252934615987 * 10 ^ 70 +
        7168102218395368048408965482550138026689193428942584583946559810876415) * 10 ^ 70 +
        6620024374018259930045380896727562891255581622282027080354271133753578) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 66 = 27 +
      39 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_193_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_194_suffix_zero :
    (∑ x ∈ Finset.range 40,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (194 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_194 :
    recurrence2Scalar1Shift.coeff 194 =
      -(((9998117862484109462476750552147970420107245541204721805411101 * 10 ^ 70 +
        4975212136300351255517878150017757126426572540801205726242469801092002) * 10 ^ 70 +
        1292085703952831462358667178912302218413590719148506557163391952452003) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 67 = 27 +
      40 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_194_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_195_suffix_zero :
    (∑ x ∈ Finset.range 41,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (195 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_195 :
    recurrence2Scalar1Shift.coeff 195 =
      -(((12061401358978954363838035692857829789395576355263491896111596 * 10 ^ 70 +
        4357647084840694932063347118023681299809807279945780927700413907969594) * 10 ^ 70 +
        2234170319067185187724590897478274400884320090305918402609298643980762) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 68 = 27 +
      41 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_195_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
