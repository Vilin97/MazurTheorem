/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupExceptionalProduct
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupC4
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar4ExceptionalPart0Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: Scalar4Exceptional coefficient convolution

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence2ExceptionalProduct_coeff_0
  recurrence2ExceptionalProduct_coeff_1
  recurrence2ExceptionalProduct_coeff_2
  recurrence2ExceptionalProduct_coeff_3
  recurrence2ExceptionalProduct_coeff_4
  recurrence2ExceptionalProduct_coeff_5
  recurrence2ExceptionalProduct_coeff_6
  recurrence2ExceptionalProduct_coeff_7
  recurrence2ExceptionalProduct_coeff_8
  recurrence2ExceptionalProduct_coeff_9
  recurrence2ExceptionalProduct_coeff_10
  recurrence2ExceptionalProduct_coeff_11
  recurrence2ExceptionalProduct_coeff_12
  recurrence2ExceptionalProduct_coeff_13
  recurrence2ExceptionalProduct_coeff_14
  recurrence2ExceptionalProduct_coeff_15
  recurrence2ExceptionalProduct_coeff_16
  recurrence2ExceptionalProduct_coeff_17
  recurrence2ExceptionalProduct_coeff_18
  recurrence2ExceptionalProduct_coeff_19
  recurrence2ExceptionalProduct_coeff_20
  recurrence2ExceptionalProduct_coeff_21
  recurrence2ExceptionalProduct_coeff_22
  recurrence2ExceptionalProduct_coeff_23
  recurrence2ExceptionalProduct_coeff_24
  recurrence2ExceptionalProduct_coeff_25
  recurrence2ExceptionalProduct_coeff_26
  recurrence2ExceptionalProduct_coeff_27
  recurrence2ExceptionalProduct_coeff_28
  recurrence2ExceptionalProduct_coeff_29
  recurrence2ExceptionalProduct_coeff_30
  recurrence2ExceptionalProduct_coeff_31
  recurrence2ExceptionalProduct_coeff_32
  recurrence2ExceptionalProduct_coeff_33
  recurrence2ExceptionalProduct_coeff_34
  recurrence2ExceptionalProduct_coeff_35
  recurrence2ExceptionalProduct_coeff_36
  recurrence2ExceptionalProduct_coeff_37
  recurrence2ExceptionalProduct_coeff_38
  recurrence2ExceptionalProduct_coeff_39
  recurrence2ExceptionalProduct_coeff_40
  recurrence2ExceptionalProduct_coeff_41
  recurrence2ExceptionalProduct_coeff_42
  recurrence2ExceptionalProduct_coeff_43
  recurrence2ExceptionalProduct_coeff_44
  recurrence2ExceptionalProduct_coeff_45
  recurrence2ExceptionalProduct_coeff_46
  recurrence2ExceptionalProduct_coeff_47
  recurrence2ExceptionalProduct_coeff_48
  recurrence2ExceptionalProduct_coeff_49
  recurrence2ExceptionalProduct_coeff_50
  recurrence2ExceptionalProduct_coeff_51
  recurrence2ExceptionalProduct_coeff_52
  recurrence2ExceptionalProduct_coeff_53
  recurrence2ExceptionalProduct_coeff_54
  recurrence2ExceptionalProduct_coeff_55
  recurrence2ExceptionalProduct_coeff_56
  recurrence2ExceptionalProduct_coeff_57
  recurrence2ExceptionalProduct_coeff_58
  recurrence2ExceptionalProduct_coeff_59
  recurrence2ExceptionalProduct_coeff_60
  recurrence2ExceptionalProduct_coeff_61
  recurrence2ExceptionalProduct_coeff_62
  recurrence2ExceptionalProduct_coeff_63
  recurrence2ExceptionalProduct_coeff_64
  recurrence2ExceptionalProduct_coeff_65
  recurrence2ExceptionalProduct_coeff_66
  recurrence2ExceptionalProduct_coeff_67
  recurrence2ExceptionalProduct_coeff_68
  recurrence2ExceptionalProduct_coeff_69
  recurrence2ExceptionalProduct_coeff_70
  recurrence2ExceptionalProduct_coeff_71
  recurrence2ExceptionalProduct_coeff_72
  recurrence2ExceptionalProduct_coeff_73
  recurrence2ExceptionalProduct_coeff_74
  recurrence2ExceptionalProduct_coeff_75
  recurrence2ExceptionalProduct_coeff_76
  recurrence2ExceptionalProduct_coeff_77
  recurrence2ExceptionalProduct_coeff_78
  recurrence2ExceptionalProduct_coeff_79
  recurrence2ExceptionalProduct_coeff_80
  recurrence2ExceptionalProduct_coeff_81
  recurrence2ExceptionalProduct_coeff_82
  recurrence2ExceptionalProduct_coeff_83
  recurrence2ExceptionalProduct_coeff_84
  recurrence2ExceptionalProduct_coeff_85
  recurrence2ExceptionalProduct_coeff_86
  recurrence2ExceptionalProduct_coeff_87
  recurrence2ExceptionalProduct_coeff_88
  recurrence2ExceptionalProduct_coeff_89
  recurrence2ExceptionalProduct_coeff_90
  recurrence2ExceptionalProduct_coeff_91
  recurrence2ExceptionalProduct_coeff_92
  recurrence2ExceptionalProduct_coeff_93
  recurrence2ExceptionalProduct_coeff_94
  recurrence2ExceptionalProduct_coeff_95
  recurrence2ExceptionalProduct_coeff_96
  recurrence2ExceptionalProduct_coeff_97
  recurrence2ExceptionalProduct_coeff_98
  recurrence2ExceptionalProduct_coeff_99
  recurrence2ExceptionalProduct_coeff_100
  recurrence2ExceptionalProduct_coeff_101
  recurrence2ExceptionalProduct_coeff_102
  recurrence2ExceptionalProduct_coeff_103
  recurrence2ExceptionalProduct_coeff_104
  recurrence2ExceptionalProduct_coeff_105
  recurrence2ExceptionalProduct_coeff_106
  recurrence2ExceptionalProduct_coeff_107
  recurrence2ExceptionalProduct_coeff_108
  recurrence2ExceptionalProduct_coeff_109
  recurrence2ExceptionalProduct_coeff_110
  recurrence2ExceptionalProduct_coeff_111
  recurrence2ExceptionalProduct_coeff_112
  recurrence2ExceptionalProduct_coeff_113
  recurrence2ExceptionalProduct_coeff_114
  recurrence2ExceptionalProduct_coeff_115
  recurrence2ExceptionalProduct_coeff_116
  recurrence2ExceptionalProduct_coeff_117
  recurrence2ExceptionalProduct_coeff_118
  recurrence2ExceptionalProduct_coeff_119
  recurrence2ExceptionalProduct_coeff_120
  recurrence2ExceptionalProduct_coeff_121
  recurrence2ExceptionalProduct_coeff_122
  recurrence2ExceptionalProduct_coeff_123
  recurrence2ExceptionalProduct_coeff_124
  recurrence2ExceptionalProduct_coeff_125
  recurrence2ExceptionalProduct_coeff_126
  recurrence2ExceptionalProduct_coeff_127
  recurrence2ExceptionalProduct_coeff_128
  recurrence2ExceptionalProduct_coeff_129
  recurrence2ExceptionalProduct_coeff_130
  recurrence2ExceptionalProduct_coeff_131
  recurrence2ExceptionalProduct_coeff_132
  recurrence2ExceptionalProduct_coeff_133
  recurrence2ExceptionalProduct_coeff_134
  recurrence2ExceptionalProduct_coeff_135
  recurrence2ExceptionalProduct_coeff_136
  recurrence2ExceptionalProduct_coeff_137
  recurrence2ExceptionalProduct_coeff_138
  recurrence2ExceptionalProduct_coeff_139
  recurrence2ExceptionalProduct_coeff_140
  recurrence2ExceptionalProduct_coeff_141
  recurrence2ExceptionalProduct_coeff_142
  recurrence2ExceptionalProduct_coeff_143
  recurrence2ExceptionalProduct_coeff_144
  recurrence2ExceptionalProduct_coeff_145
  recurrence2ExceptionalProduct_coeff_146
  recurrence2ExceptionalProduct_coeff_147
  recurrence2ExceptionalProduct_coeff_148
  recurrence2ExceptionalProduct_coeff_149
  recurrence2ExceptionalProduct_coeff_150
  recurrence2ExceptionalProduct_coeff_151
  recurrence2ExceptionalProduct_coeff_152
  recurrence2ExceptionalProduct_coeff_153
  recurrence2ExceptionalProduct_coeff_154
  recurrence2ExceptionalProduct_coeff_155
  recurrence2ExceptionalProduct_coeff_156
  recurrence2ExceptionalProduct_coeff_157
  recurrence2ExceptionalProduct_coeff_158
  recurrence2ExceptionalProduct_coeff_159
  recurrence2ExceptionalProduct_coeff_160
  recurrence2ExceptionalProduct_coeff_161
  recurrence2ExceptionalProduct_coeff_162
  recurrence2ExceptionalProduct_coeff_163
  recurrence2ExceptionalProduct_coeff_164
  recurrence2ExceptionalProduct_coeff_165
  recurrence2ExceptionalProduct_coeff_166
  recurrence2ExceptionalProduct_coeff_167
  recurrence2ExceptionalProduct_coeff_168
  recurrence2ExceptionalProduct_coeff_169
  recurrence2ExceptionalProduct_coeff_170
  recurrence2ExceptionalProduct_coeff_171
  recurrence2ExceptionalProduct_coeff_172
  recurrence2ExceptionalProduct_coeff_173
  recurrence2ExceptionalProduct_coeff_174
  recurrence2ExceptionalProduct_coeff_175
  recurrence2ExceptionalProduct_coeff_176
  recurrence2ExceptionalProduct_coeff_177
  recurrence2ExceptionalProduct_coeff_178
  recurrence2ExceptionalProduct_coeff_179
  recurrence2ExceptionalProduct_coeff_180
  recurrence2ExceptionalProduct_coeff_181
  recurrence2ExceptionalProduct_coeff_182
  recurrence2ExceptionalProduct_coeff_183
  recurrence2ExceptionalProduct_coeff_184
  recurrence2ExceptionalProduct_coeff_185
  recurrence2ExceptionalProduct_coeff_186
  recurrence2ExceptionalProduct_coeff_187
  recurrence2ExceptionalProduct_coeff_188
  recurrence2ExceptionalProduct_coeff_189
  recurrence2ExceptionalProduct_coeff_190
  recurrence2ExceptionalProduct_coeff_191
  recurrence2ExceptionalProduct_coeff_192
  recurrence2ExceptionalProduct_coeff_193
  recurrence2C4_coeff_0
  recurrence2C4_coeff_1
  recurrence2C4_coeff_2
  recurrence2C4_coeff_3
  recurrence2C4_coeff_4
  recurrence2C4_coeff_5
  recurrence2C4_coeff_6
  recurrence2C4_coeff_7
  recurrence2C4_coeff_8
  recurrence2C4_coeff_9
  recurrence2C4_coeff_10
  recurrence2C4_coeff_11
  recurrence2C4_coeff_12
  recurrence2C4_coeff_13
  recurrence2C4_coeff_14
  recurrence2C4_coeff_15
  recurrence2C4_coeff_16
  recurrence2C4_coeff_17
  recurrence2C4_coeff_18
  recurrence2C4_coeff_19
  recurrence2C4_coeff_20
  recurrence2C4_coeff_21
  recurrence2C4_coeff_22
  recurrence2C4_coeff_23
  recurrence2C4_coeff_24
  recurrence2C4_coeff_25
  recurrence2C4_coeff_26
  recurrence2C4_coeff_27
  recurrence2C4_coeff_28
  recurrence2C4_coeff_29
  recurrence2C4_coeff_30
  recurrence2C4_coeff_31
  recurrence2C4_coeff_32
  recurrence2C4_coeff_33
  recurrence2C4_coeff_34
  recurrence2C4_coeff_35
  recurrence2C4_coeff_36
  recurrence2C4_coeff_37
  recurrence2C4_coeff_38
  recurrence2C4_coeff_39
  recurrence2C4_coeff_40
  recurrence2C4_coeff_41
  recurrence2C4_coeff_42
  recurrence2C4_coeff_43
  recurrence2C4_coeff_44
  recurrence2C4_coeff_45
  recurrence2C4_coeff_46
  recurrence2C4_coeff_47
  recurrence2C4_coeff_48
  recurrence2C4_coeff_49
  recurrence2C4_coeff_50
  recurrence2C4_coeff_51
  recurrence2C4_coeff_52
  recurrence2C4_coeff_53
  recurrence2C4_coeff_54
  recurrence2C4_coeff_55
  recurrence2C4_coeff_56
  recurrence2C4_coeff_57
  recurrence2C4_coeff_58
  recurrence2C4_coeff_59
  recurrence2C4_coeff_60
  recurrence2C4_coeff_61
  recurrence2C4_coeff_62
  recurrence2C4_coeff_63
  recurrence2C4_coeff_64
  recurrence2C4_coeff_65
  recurrence2C4_coeff_66
  recurrence2C4_coeff_67
  recurrence2C4_coeff_68
  recurrence2C4_coeff_69
  recurrence2C4_coeff_70
  recurrence2C4_coeff_71
  recurrence2C4_coeff_72
  recurrence2C4_coeff_73
  recurrence2C4_coeff_74
  recurrence2C4_coeff_75
  recurrence2C4_coeff_76
  recurrence2C4_coeff_77
  recurrence2C4_coeff_78
  recurrence2C4_coeff_79
  recurrence2C4_coeff_80
  recurrence2C4_coeff_81
  recurrence2C4_coeff_82
  recurrence2C4_coeff_83
  recurrence2C4_coeff_84
  recurrence2C4_coeff_85
  recurrence2C4_coeff_86
  recurrence2C4_coeff_87
  recurrence2C4_coeff_88
  recurrence2C4_coeff_89
  recurrence2C4_coeff_90
  recurrence2C4_coeff_91
  recurrence2C4_coeff_92
  recurrence2C4_coeff_93
  recurrence2C4_coeff_94
  recurrence2C4_coeff_95
  recurrence2C4_coeff_96
  recurrence2C4_coeff_97
  recurrence2C4_coeff_98
  recurrence2C4_coeff_99
  recurrence2C4_coeff_100
  recurrence2C4_coeff_101
  recurrence2C4_coeff_102
  recurrence2C4_coeff_103
  recurrence2C4_coeff_104
  recurrence2C4_coeff_105
  recurrence2C4_coeff_106
  recurrence2C4_coeff_107
  recurrence2C4_coeff_108
  recurrence2C4_coeff_109
  recurrence2C4_coeff_110
  recurrence2C4_coeff_111
  recurrence2C4_coeff_112
  recurrence2C4_coeff_113
  recurrence2C4_coeff_114
  recurrence2C4_coeff_115
  recurrence2C4_coeff_116
  recurrence2C4_coeff_117
  recurrence2C4_coeff_118
  recurrence2C4_coeff_119
  recurrence2C4_coeff_120
  recurrence2C4_coeff_121
  recurrence2C4_coeff_122
  recurrence2C4_coeff_123
  recurrence2C4_coeff_124
  recurrence2C4_coeff_125
  recurrence2C4_coeff_126
  recurrence2C4_coeff_127
  recurrence2C4_coeff_128
  recurrence2C4_coeff_129
  recurrence2C4_coeff_130
  recurrence2C4_coeff_131
  recurrence2C4_coeff_132
  recurrence2C4_coeff_133
  recurrence2C4_coeff_134
  recurrence2C4_coeff_135
  recurrence2C4_coeff_136
  recurrence2C4_coeff_137
  recurrence2C4_coeff_138
  recurrence2C4_coeff_139
  recurrence2C4_coeff_140
  recurrence2C4_coeff_141
  recurrence2C4_coeff_142
  recurrence2C4_coeff_143
  recurrence2C4_coeff_144
  recurrence2C4_coeff_145
  recurrence2C4_coeff_146
  recurrence2C4_coeff_147
  recurrence2C4_coeff_148
  recurrence2C4_coeff_149
  recurrence2C4_coeff_150
  recurrence2C4_coeff_151
  recurrence2C4_coeff_152
  recurrence2C4_coeff_153
  recurrence2C4_coeff_154
  recurrence2C4_coeff_155
  recurrence2C4_coeff_156
  recurrence2C4_coeff_157
  recurrence2C4_coeff_158
  recurrence2C4_coeff_159
  recurrence2C4_coeff_160
  recurrence2C4_coeff_161
  recurrence2C4_coeff_162
  recurrence2C4_coeff_163
  recurrence2C4_coeff_164
  recurrence2C4_coeff_165
  recurrence2C4_coeff_166
  recurrence2C4_coeff_167
  recurrence2C4_coeff_168
  recurrence2C4_coeff_169
  recurrence2C4_coeff_170
  recurrence2C4_coeff_171
  recurrence2C4_coeff_172
  recurrence2C4_coeff_173
  recurrence2C4_coeff_174
  recurrence2C4_coeff_175
  recurrence2C4_coeff_176
  recurrence2C4_coeff_177
  recurrence2C4_coeff_178

private theorem recurrence2Scalar4Exceptional_coeff_199_prefix_zero :
    (∑ x ∈ Finset.range 21,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (199 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (199 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_199_suffix_zero :
    (∑ x ∈ Finset.range 6,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (199 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_199 :
    recurrence2Scalar4Exceptional.coeff 199 =
      (((971418756180957101299512599038572722132966319218807262192 * 10 ^ 70 +
        4465670658807102221860822282011563137166673542812656202806004602578661) * 10 ^ 70 +
        3989161024549999633222128039500713466977639121053753180771064390579796) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 200 = 21 +
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
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 13 +
      6 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_199_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_199_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Exceptional_coeff_200_prefix_zero :
    (∑ x ∈ Finset.range 22,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (200 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (200 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_200_suffix_zero :
    (∑ x ∈ Finset.range 7,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (200 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_200 :
    recurrence2Scalar4Exceptional.coeff 200 =
      -(((2051659938405932514795905238730171107973950336276057282072 * 10 ^ 70 +
        3453202077198186703125595197621912303190074476030696474925461501853701) * 10 ^ 70 +
        6285432695776831354380930772268941944562768188127523449784212612432633) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 201 = 22 +
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
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 12 +
      7 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_200_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_200_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Exceptional_coeff_201_prefix_zero :
    (∑ x ∈ Finset.range 23,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (201 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (201 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_201_suffix_zero :
    (∑ x ∈ Finset.range 8,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (201 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_201 :
    recurrence2Scalar4Exceptional.coeff 201 =
      (((3522330384359744972281087240950861426186346301733842341836 * 10 ^ 70 +
        0258900584470586621361324409289564698878131136909439671463822951683408) * 10 ^ 70 +
        0456364465764334085451505761233369223552810631613567148373512509268934) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 202 = 23 +
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
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 11 +
      8 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_201_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_201_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Exceptional_coeff_202_prefix_zero :
    (∑ x ∈ Finset.range 24,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (202 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (202 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_202_suffix_zero :
    (∑ x ∈ Finset.range 9,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (202 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_202 :
    recurrence2Scalar4Exceptional.coeff 202 =
      -(((5286840845243382193652705389759854702617079888339165094514 * 10 ^ 70 +
        5008476882234783757270810253787357541598281050955677341416018368376227) * 10 ^ 70 +
        7676689783777010061567088154122139599116521435855343267943503897635403) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 203 = 24 +
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
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 10 +
      9 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_202_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_202_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Exceptional_coeff_203_prefix_zero :
    (∑ x ∈ Finset.range 25,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (203 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (203 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_203_suffix_zero :
    (∑ x ∈ Finset.range 10,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (203 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_203 :
    recurrence2Scalar4Exceptional.coeff 203 =
      (((7122561807244533584703748027190165742204744452527023701411 * 10 ^ 70 +
        5954013255641203648862783486318453701152263775809245216939489193167790) * 10 ^ 70 +
        7608654629809249781123740255992647846360222793985689201101987159738359) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 204 = 25 +
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
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 9 +
      10 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_203_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_203_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Exceptional_coeff_204_prefix_zero :
    (∑ x ∈ Finset.range 26,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (204 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (204 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_204_suffix_zero :
    (∑ x ∈ Finset.range 11,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (204 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_204 :
    recurrence2Scalar4Exceptional.coeff 204 =
      -(((8683482250700695774933797174154434518837714295302252030450 * 10 ^ 70 +
        6676138695782130926958597601031999811944783656165430913311574333457642) * 10 ^ 70 +
        1941245591930598508855724500916095364571979607449399198855998511987672) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 205 = 26 +
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
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 8 +
      11 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_204_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_204_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Exceptional_coeff_205_prefix_zero :
    (∑ x ∈ Finset.range 27,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (205 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (205 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_205_suffix_zero :
    (∑ x ∈ Finset.range 12,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (205 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_205 :
    recurrence2Scalar4Exceptional.coeff 205 =
      (((9541622888045400482724027187639224223100380547355407571831 * 10 ^ 70 +
        4054502829921648682898941310508073646067116881386492231840835553311825) * 10 ^ 70 +
        8005278154951915802762999866113269077451826277613910826268696386235100) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 206 = 27 +
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
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 7 +
      12 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_205_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_205_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Exceptional_coeff_206_prefix_zero :
    (∑ x ∈ Finset.range 28,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (206 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (206 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_206_suffix_zero :
    (∑ x ∈ Finset.range 13,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (206 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_206 :
    recurrence2Scalar4Exceptional.coeff 206 =
      -(((9268605263099206561811066987499165749154736045435978528040 * 10 ^ 70 +
        5984547302203980831262278650106577065705107003173781691084674837093744) * 10 ^ 70 +
        7501659314678330665166867491103581693119559681663430794814799850146164) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 207 = 28 +
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
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 6 +
      13 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_206_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_206_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Exceptional_coeff_207_prefix_zero :
    (∑ x ∈ Finset.range 29,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (207 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (207 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_207_suffix_zero :
    (∑ x ∈ Finset.range 14,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (207 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_207 :
    recurrence2Scalar4Exceptional.coeff 207 =
      (((7545093881043087290914634183830861911880494892548254445055 * 10 ^ 70 +
        4179492837785865483029216408547828321871185326939415779226964011716950) * 10 ^ 70 +
        2765819486462297580523780901108149460333942930100807187987684701889545) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 208 = 29 +
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
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 5 +
      14 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_207_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_207_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Exceptional_coeff_208_prefix_zero :
    (∑ x ∈ Finset.range 30,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (208 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (208 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_208_suffix_zero :
    (∑ x ∈ Finset.range 15,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (208 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_208 :
    recurrence2Scalar4Exceptional.coeff 208 =
      -(((4272306715210433442484308872735424477047109817493192467111 * 10 ^ 70 +
        0269666175428778691315990942112797595335231434355703445565279376489157) * 10 ^ 70 +
        3894051175330011326232772061527871447383148308727336025348920043580305) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 209 = 30 +
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
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 4 +
      15 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_208_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_208_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Exceptional_coeff_209_prefix_zero :
    (∑ x ∈ Finset.range 31,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (209 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (209 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_209_suffix_zero :
    (∑ x ∈ Finset.range 16,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (209 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_209 :
    recurrence2Scalar4Exceptional.coeff 209 =
      -(((348135611787495140812079446480913018284653604059776376065 * 10 ^ 70 +
        8965328951880209472715033720954310919718859454072478519965921071991266) * 10 ^ 70 +
        8726693718332823775683931373661386709862422357381575162604995216902515) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 210 = 31 +
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
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 3 +
      16 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_209_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_209_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Exceptional_coeff_210_prefix_zero :
    (∑ x ∈ Finset.range 32,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (210 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (210 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_210_suffix_zero :
    (∑ x ∈ Finset.range 17,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (210 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_210 :
    recurrence2Scalar4Exceptional.coeff 210 =
      (((5797499422059624264665567766971807002941017433622657724582 * 10 ^ 70 +
        2353721756925689333253146236165143804812725256810111012109936859803450) * 10 ^ 70 +
        1103929303879882200101659206734693720351558702966548005581619275146358) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 211 = 32 +
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
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 2 +
      17 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_210_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_210_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Exceptional_coeff_211_prefix_zero :
    (∑ x ∈ Finset.range 33,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (211 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (211 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_211_suffix_zero :
    (∑ x ∈ Finset.range 18,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (211 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_211 :
    recurrence2Scalar4Exceptional.coeff 211 =
      -(((11303921384775451023876799450134094119699238613837056807654 * 10 ^ 70 +
        1404413802688975028132497198774975948300541156832573951811461594289917) * 10 ^ 70 +
        3991752104867119758485634281804661558155533737938850172735567673815115) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 212 = 33 +
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
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 1 +
      18 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_211_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_211_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Exceptional_coeff_212_prefix_zero :
    (∑ x ∈ Finset.range 34,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (212 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (212 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_212_suffix_zero :
    (∑ x ∈ Finset.range 19,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (212 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_212 :
    recurrence2Scalar4Exceptional.coeff 212 =
      (((15981973015726569468511661300433570967338387075577045136778 * 10 ^ 70 +
        4290061251382911833844639859244316365919852228979259778927304159798213) * 10 ^ 70 +
        7370543345497513223430293317143612673742779791274143402856792641775010) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 213 = 34 +
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
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_212_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_212_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Exceptional_coeff_213_prefix_zero :
    (∑ x ∈ Finset.range 35,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (213 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (213 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_213_suffix_zero :
    (∑ x ∈ Finset.range 20,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (213 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_213 :
    recurrence2Scalar4Exceptional.coeff 213 =
      -(((19018218408017571183934081154745843615292065405605147130175 * 10 ^ 70 +
        2054977771154128360929412047136450889703477291616332394918800294904304) * 10 ^ 70 +
        0284738124199596708120728757800617601844235319373491014121419234255498) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 214 = 35 +
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
    rw [show 51 = 31 +
      20 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_213_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_213_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Exceptional_coeff_214_prefix_zero :
    (∑ x ∈ Finset.range 36,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (214 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (214 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_214_suffix_zero :
    (∑ x ∈ Finset.range 21,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (214 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_214 :
    recurrence2Scalar4Exceptional.coeff 214 =
      (((19855579923513743746291350177681090057744836027476694800346 * 10 ^ 70 +
        4979682420646924411526772731965448805182876378705781939325296199672842) * 10 ^ 70 +
        6339116182863835441016423373845435079529960831597798963248441895962801) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 215 = 36 +
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
    rw [show 51 = 30 +
      21 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_214_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_214_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Exceptional_coeff_215_prefix_zero :
    (∑ x ∈ Finset.range 37,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (215 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (215 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_215_suffix_zero :
    (∑ x ∈ Finset.range 22,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (215 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_215 :
    recurrence2Scalar4Exceptional.coeff 215 =
      -(((18325680133337420662329403676992757014404031373825651808765 * 10 ^ 70 +
        7358946642099168737201457193682191479196826611363671109495390050622676) * 10 ^ 70 +
        4653886366759708591007521817950743536992600747998469353164882508936721) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 216 = 37 +
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
    rw [show 51 = 29 +
      22 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_215_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_215_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Exceptional_coeff_216_prefix_zero :
    (∑ x ∈ Finset.range 38,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (216 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (216 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_216_suffix_zero :
    (∑ x ∈ Finset.range 23,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (216 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_216 :
    recurrence2Scalar4Exceptional.coeff 216 =
      (((14691045649607999784326371017787007355760205088889332654576 * 10 ^ 70 +
        8194239976256917378442701680239241071613920687384956514944766437129215) * 10 ^ 70 +
        1054979057390052838903739333584698297827409183809704695351459267954904) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 217 = 38 +
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
    rw [show 51 = 28 +
      23 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_216_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_216_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Exceptional_coeff_217_prefix_zero :
    (∑ x ∈ Finset.range 39,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (217 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (217 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_217_suffix_zero :
    (∑ x ∈ Finset.range 24,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (217 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_217 :
    recurrence2Scalar4Exceptional.coeff 217 =
      -(((9584566060753889679357543140180253504725830325122748494091 * 10 ^ 70 +
        9584736767781182590535257797371868806873247977562013353921255535155324) * 10 ^ 70 +
        3907313687324623426607847004159751055403513070329942690783991299028913) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 218 = 39 +
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
  rw [recurrence2Scalar4Exceptional_coeff_217_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_217_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Exceptional_coeff_218_prefix_zero :
    (∑ x ∈ Finset.range 40,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (218 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (218 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_218_suffix_zero :
    (∑ x ∈ Finset.range 25,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (218 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_218 :
    recurrence2Scalar4Exceptional.coeff 218 =
      (((3863454284969980283377188096789395655490692622981033804189 * 10 ^ 70 +
        2089067876185165996302626800679717802329050962010298577296477002230905) * 10 ^ 70 +
        8742965028868003520614332032549443220235052816637008745687615315212611) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 219 = 40 +
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
    rw [show 51 = 26 +
      25 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_218_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_218_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Exceptional_coeff_219_prefix_zero :
    (∑ x ∈ Finset.range 41,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (219 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (219 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_219_suffix_zero :
    (∑ x ∈ Finset.range 26,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (219 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_219 :
    recurrence2Scalar4Exceptional.coeff 219 =
      (((1580980924797705480744710123791640071368909661645928936646 * 10 ^ 70 +
        5171923365514235818822107623220815863604107745850226286333930859001368) * 10 ^ 70 +
        0979819724811744241862221220768269495233062069376857438525010666748819) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 220 = 41 +
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
    rw [show 51 = 25 +
      26 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_219_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_219_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Exceptional_coeff_220_prefix_zero :
    (∑ x ∈ Finset.range 42,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (220 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (220 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_220_suffix_zero :
    (∑ x ∈ Finset.range 27,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (220 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_220 :
    recurrence2Scalar4Exceptional.coeff 220 =
      -(((6006077437941323644480685065930613794457795717558526850884 * 10 ^ 70 +
        6531938385924799664656054505760662860015523068774365700578319547806095) * 10 ^ 70 +
        5096634436464637133573754594317006406580752854096948984362414020579760) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 221 = 42 +
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
    rw [show 51 = 24 +
      27 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_220_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_220_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Exceptional_coeff_221_prefix_zero :
    (∑ x ∈ Finset.range 43,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (221 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (221 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_221_suffix_zero :
    (∑ x ∈ Finset.range 28,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (221 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_221 :
    recurrence2Scalar4Exceptional.coeff 221 =
      (((8947480312828402986922632891180827522608485628562376042751 * 10 ^ 70 +
        5036139825141760313643814480927780892384772363738270583915993294771204) * 10 ^ 70 +
        8079594822625272429174392632734867001884047793638526270870383061582242) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 222 = 43 +
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
    rw [show 51 = 23 +
      28 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_221_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_221_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Exceptional_coeff_222_prefix_zero :
    (∑ x ∈ Finset.range 44,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (222 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (222 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_222_suffix_zero :
    (∑ x ∈ Finset.range 29,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (222 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_222 :
    recurrence2Scalar4Exceptional.coeff 222 =
      -(((10269423319194229880520883326404986677704385614345727049125 * 10 ^ 70 +
        7734646404203192577095278503144226846399676558165713268768023044120988) * 10 ^ 70 +
        3319773626819006172356894364463676348304474880624802768509348577347212) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 223 = 44 +
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
    rw [show 51 = 22 +
      29 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_222_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_222_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Exceptional_coeff_223_prefix_zero :
    (∑ x ∈ Finset.range 45,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (223 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (223 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_223_suffix_zero :
    (∑ x ∈ Finset.range 30,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (223 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_223 :
    recurrence2Scalar4Exceptional.coeff 223 =
      (((10134321802662813010263617223579950786128638634082267663589 * 10 ^ 70 +
        4708265686835933925815015844293692431047119773917405389093860856058307) * 10 ^ 70 +
        4897573822650027085357345794974237496082145330950458509388629748716239) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 224 = 45 +
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
    rw [show 51 = 21 +
      30 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_223_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_223_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Exceptional_coeff_224_prefix_zero :
    (∑ x ∈ Finset.range 46,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (224 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (224 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_224_suffix_zero :
    (∑ x ∈ Finset.range 31,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (224 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_224 :
    recurrence2Scalar4Exceptional.coeff 224 =
      -(((8912369251311182115322244623456193040099545239745026970485 * 10 ^ 70 +
        8321390072064130037180680202239782893264882753702245180823182241831485) * 10 ^ 70 +
        0437475997810214965099275196231361696204928775609828963939337718888007) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 225 = 46 +
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
    rw [show 51 = 20 +
      31 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_224_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_224_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Exceptional_coeff_225_prefix_zero :
    (∑ x ∈ Finset.range 47,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (225 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (225 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_225_suffix_zero :
    (∑ x ∈ Finset.range 32,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (225 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_225 :
    recurrence2Scalar4Exceptional.coeff 225 =
      (((7064322422984259091895334622238664619606426463937167799438 * 10 ^ 70 +
        9609885381130153001339250944355526244695293228710929078381612639480815) * 10 ^ 70 +
        9084674728125521208330596495967670772976390714335163408887585195212069) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 226 = 47 +
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
  rw [recurrence2Scalar4Exceptional_coeff_225_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_225_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Exceptional_coeff_226_prefix_zero :
    (∑ x ∈ Finset.range 48,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (226 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (226 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_226_suffix_zero :
    (∑ x ∈ Finset.range 33,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (226 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_226 :
    recurrence2Scalar4Exceptional.coeff 226 =
      -(((5031313772558879349981628386535455786204448899318672914174 * 10 ^ 70 +
        2976715810083566383777710939794399340065602792732540867395987199157881) * 10 ^ 70 +
        1957553941836871392082621265583211986797513076964538277807201973015973) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 227 = 48 +
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
    rw [show 51 = 18 +
      33 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_226_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_226_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Exceptional_coeff_227_prefix_zero :
    (∑ x ∈ Finset.range 49,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (227 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (227 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_227_suffix_zero :
    (∑ x ∈ Finset.range 34,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (227 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_227 :
    recurrence2Scalar4Exceptional.coeff 227 =
      (((3156363147052915624012906863003185055262887260065674140895 * 10 ^ 70 +
        8609266369692650102598413020150336552371446613346827386349738884823792) * 10 ^ 70 +
        0174110153319859106957932739352163813460738844078898243080541124752205) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 228 = 49 +
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
    rw [show 51 = 17 +
      34 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_227_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_227_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Exceptional_coeff_228_prefix_zero :
    (∑ x ∈ Finset.range 50,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (228 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (228 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_228_suffix_zero :
    (∑ x ∈ Finset.range 35,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (228 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_228 :
    recurrence2Scalar4Exceptional.coeff 228 =
      -(((1648135293194997571158356728926270553708745901875360116580 * 10 ^ 70 +
        7151288392580466252009797596175441907259244726597418579240271191143970) * 10 ^ 70 +
        5827610989374421678765136566130910428557903019624231496134517052091211) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 229 = 50 +
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
    rw [show 51 = 16 +
      35 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_228_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_228_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Exceptional_coeff_229_prefix_zero :
    (∑ x ∈ Finset.range 51,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (229 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (229 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_229_suffix_zero :
    (∑ x ∈ Finset.range 36,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (229 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_229 :
    recurrence2Scalar4Exceptional.coeff 229 =
      (((583838539178580256363199143168787037339531171033897062861 * 10 ^ 70 +
        7781555156541236594691950136884195805206009298144324678464574287152015) * 10 ^ 70 +
        6103476088269012072772662329227010176865543517602031482644930218382484) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 230 = 51 +
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
    rw [show 51 = 15 +
      36 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_229_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_229_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
