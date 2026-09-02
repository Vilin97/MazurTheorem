/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB1
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB3A4
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar2FirstPart0Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar2First coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4B1_coeff_1
  recurrence4B1_coeff_10
  recurrence4B1_coeff_100
  recurrence4B1_coeff_101
  recurrence4B1_coeff_102
  recurrence4B1_coeff_103
  recurrence4B1_coeff_104
  recurrence4B1_coeff_105
  recurrence4B1_coeff_106
  recurrence4B1_coeff_107
  recurrence4B1_coeff_108
  recurrence4B1_coeff_109
  recurrence4B1_coeff_11
  recurrence4B1_coeff_110
  recurrence4B1_coeff_111
  recurrence4B1_coeff_112
  recurrence4B1_coeff_113
  recurrence4B1_coeff_114
  recurrence4B1_coeff_115
  recurrence4B1_coeff_116
  recurrence4B1_coeff_117
  recurrence4B1_coeff_118
  recurrence4B1_coeff_119
  recurrence4B1_coeff_12
  recurrence4B1_coeff_120
  recurrence4B1_coeff_121
  recurrence4B1_coeff_122
  recurrence4B1_coeff_123
  recurrence4B1_coeff_124
  recurrence4B1_coeff_125
  recurrence4B1_coeff_126
  recurrence4B1_coeff_127
  recurrence4B1_coeff_128
  recurrence4B1_coeff_129
  recurrence4B1_coeff_13
  recurrence4B1_coeff_130
  recurrence4B1_coeff_131
  recurrence4B1_coeff_132
  recurrence4B1_coeff_133
  recurrence4B1_coeff_134
  recurrence4B1_coeff_135
  recurrence4B1_coeff_136
  recurrence4B1_coeff_137
  recurrence4B1_coeff_138
  recurrence4B1_coeff_139
  recurrence4B1_coeff_14
  recurrence4B1_coeff_140
  recurrence4B1_coeff_141
  recurrence4B1_coeff_142
  recurrence4B1_coeff_143
  recurrence4B1_coeff_144
  recurrence4B1_coeff_145
  recurrence4B1_coeff_146
  recurrence4B1_coeff_147
  recurrence4B1_coeff_148
  recurrence4B1_coeff_149
  recurrence4B1_coeff_15
  recurrence4B1_coeff_150
  recurrence4B1_coeff_151
  recurrence4B1_coeff_152
  recurrence4B1_coeff_153
  recurrence4B1_coeff_154
  recurrence4B1_coeff_155
  recurrence4B1_coeff_156

attribute [local simp]
  recurrence4B1_coeff_157
  recurrence4B1_coeff_158
  recurrence4B1_coeff_159
  recurrence4B1_coeff_16
  recurrence4B1_coeff_160
  recurrence4B1_coeff_161
  recurrence4B1_coeff_162
  recurrence4B1_coeff_163
  recurrence4B1_coeff_164
  recurrence4B1_coeff_165
  recurrence4B1_coeff_166
  recurrence4B1_coeff_167
  recurrence4B1_coeff_168
  recurrence4B1_coeff_169
  recurrence4B1_coeff_17
  recurrence4B1_coeff_170
  recurrence4B1_coeff_18
  recurrence4B1_coeff_19
  recurrence4B1_coeff_2
  recurrence4B1_coeff_20
  recurrence4B1_coeff_21
  recurrence4B1_coeff_22
  recurrence4B1_coeff_23
  recurrence4B1_coeff_24
  recurrence4B1_coeff_25
  recurrence4B1_coeff_26
  recurrence4B1_coeff_27
  recurrence4B1_coeff_28
  recurrence4B1_coeff_29
  recurrence4B1_coeff_3
  recurrence4B1_coeff_30
  recurrence4B1_coeff_31
  recurrence4B1_coeff_32
  recurrence4B1_coeff_33
  recurrence4B1_coeff_34
  recurrence4B1_coeff_35
  recurrence4B1_coeff_36
  recurrence4B1_coeff_37
  recurrence4B1_coeff_38
  recurrence4B1_coeff_39
  recurrence4B1_coeff_4
  recurrence4B1_coeff_40
  recurrence4B1_coeff_41
  recurrence4B1_coeff_42
  recurrence4B1_coeff_43
  recurrence4B1_coeff_44
  recurrence4B1_coeff_45
  recurrence4B1_coeff_46
  recurrence4B1_coeff_47
  recurrence4B1_coeff_48
  recurrence4B1_coeff_49
  recurrence4B1_coeff_5
  recurrence4B1_coeff_50
  recurrence4B1_coeff_51
  recurrence4B1_coeff_52
  recurrence4B1_coeff_53
  recurrence4B1_coeff_54
  recurrence4B1_coeff_55
  recurrence4B1_coeff_56
  recurrence4B1_coeff_57
  recurrence4B1_coeff_58
  recurrence4B1_coeff_59
  recurrence4B1_coeff_6
  recurrence4B1_coeff_60

attribute [local simp]
  recurrence4B1_coeff_61
  recurrence4B1_coeff_62
  recurrence4B1_coeff_63
  recurrence4B1_coeff_64
  recurrence4B1_coeff_65
  recurrence4B1_coeff_66
  recurrence4B1_coeff_67
  recurrence4B1_coeff_68
  recurrence4B1_coeff_69
  recurrence4B1_coeff_7
  recurrence4B1_coeff_70
  recurrence4B1_coeff_71
  recurrence4B1_coeff_72
  recurrence4B1_coeff_73
  recurrence4B1_coeff_74
  recurrence4B1_coeff_75
  recurrence4B1_coeff_76
  recurrence4B1_coeff_77
  recurrence4B1_coeff_78
  recurrence4B1_coeff_79
  recurrence4B1_coeff_8
  recurrence4B1_coeff_80
  recurrence4B1_coeff_81
  recurrence4B1_coeff_82
  recurrence4B1_coeff_83
  recurrence4B1_coeff_84
  recurrence4B1_coeff_85
  recurrence4B1_coeff_86
  recurrence4B1_coeff_87
  recurrence4B1_coeff_88
  recurrence4B1_coeff_89
  recurrence4B1_coeff_9
  recurrence4B1_coeff_90
  recurrence4B1_coeff_91
  recurrence4B1_coeff_92
  recurrence4B1_coeff_93
  recurrence4B1_coeff_94
  recurrence4B1_coeff_95
  recurrence4B1_coeff_96
  recurrence4B1_coeff_97
  recurrence4B1_coeff_98
  recurrence4B1_coeff_99
  recurrence4B3A4_coeff_0
  recurrence4B3A4_coeff_1
  recurrence4B3A4_coeff_10
  recurrence4B3A4_coeff_100
  recurrence4B3A4_coeff_101
  recurrence4B3A4_coeff_102
  recurrence4B3A4_coeff_103
  recurrence4B3A4_coeff_104
  recurrence4B3A4_coeff_105
  recurrence4B3A4_coeff_106
  recurrence4B3A4_coeff_107
  recurrence4B3A4_coeff_108
  recurrence4B3A4_coeff_109
  recurrence4B3A4_coeff_11
  recurrence4B3A4_coeff_110
  recurrence4B3A4_coeff_111
  recurrence4B3A4_coeff_112
  recurrence4B3A4_coeff_113
  recurrence4B3A4_coeff_114
  recurrence4B3A4_coeff_115
  recurrence4B3A4_coeff_116
  recurrence4B3A4_coeff_117

attribute [local simp]
  recurrence4B3A4_coeff_118
  recurrence4B3A4_coeff_119
  recurrence4B3A4_coeff_12
  recurrence4B3A4_coeff_120
  recurrence4B3A4_coeff_121
  recurrence4B3A4_coeff_122
  recurrence4B3A4_coeff_123
  recurrence4B3A4_coeff_124
  recurrence4B3A4_coeff_125
  recurrence4B3A4_coeff_126
  recurrence4B3A4_coeff_127
  recurrence4B3A4_coeff_128
  recurrence4B3A4_coeff_129
  recurrence4B3A4_coeff_13
  recurrence4B3A4_coeff_130
  recurrence4B3A4_coeff_131
  recurrence4B3A4_coeff_132
  recurrence4B3A4_coeff_133
  recurrence4B3A4_coeff_134
  recurrence4B3A4_coeff_135
  recurrence4B3A4_coeff_136
  recurrence4B3A4_coeff_137
  recurrence4B3A4_coeff_138
  recurrence4B3A4_coeff_139
  recurrence4B3A4_coeff_14
  recurrence4B3A4_coeff_140
  recurrence4B3A4_coeff_141
  recurrence4B3A4_coeff_142
  recurrence4B3A4_coeff_143
  recurrence4B3A4_coeff_144
  recurrence4B3A4_coeff_145
  recurrence4B3A4_coeff_146
  recurrence4B3A4_coeff_147
  recurrence4B3A4_coeff_148
  recurrence4B3A4_coeff_149
  recurrence4B3A4_coeff_15
  recurrence4B3A4_coeff_150
  recurrence4B3A4_coeff_151
  recurrence4B3A4_coeff_152
  recurrence4B3A4_coeff_153
  recurrence4B3A4_coeff_154
  recurrence4B3A4_coeff_155
  recurrence4B3A4_coeff_156
  recurrence4B3A4_coeff_157
  recurrence4B3A4_coeff_158
  recurrence4B3A4_coeff_159
  recurrence4B3A4_coeff_16
  recurrence4B3A4_coeff_160
  recurrence4B3A4_coeff_161
  recurrence4B3A4_coeff_162
  recurrence4B3A4_coeff_163
  recurrence4B3A4_coeff_164
  recurrence4B3A4_coeff_165
  recurrence4B3A4_coeff_166
  recurrence4B3A4_coeff_167
  recurrence4B3A4_coeff_168
  recurrence4B3A4_coeff_169
  recurrence4B3A4_coeff_17
  recurrence4B3A4_coeff_18
  recurrence4B3A4_coeff_19
  recurrence4B3A4_coeff_2
  recurrence4B3A4_coeff_20
  recurrence4B3A4_coeff_21
  recurrence4B3A4_coeff_22

attribute [local simp]
  recurrence4B3A4_coeff_23
  recurrence4B3A4_coeff_24
  recurrence4B3A4_coeff_25
  recurrence4B3A4_coeff_26
  recurrence4B3A4_coeff_27
  recurrence4B3A4_coeff_28
  recurrence4B3A4_coeff_29
  recurrence4B3A4_coeff_3
  recurrence4B3A4_coeff_30
  recurrence4B3A4_coeff_31
  recurrence4B3A4_coeff_32
  recurrence4B3A4_coeff_33
  recurrence4B3A4_coeff_34
  recurrence4B3A4_coeff_35
  recurrence4B3A4_coeff_36
  recurrence4B3A4_coeff_37
  recurrence4B3A4_coeff_38
  recurrence4B3A4_coeff_39
  recurrence4B3A4_coeff_4
  recurrence4B3A4_coeff_40
  recurrence4B3A4_coeff_41
  recurrence4B3A4_coeff_42
  recurrence4B3A4_coeff_43
  recurrence4B3A4_coeff_44
  recurrence4B3A4_coeff_45
  recurrence4B3A4_coeff_46
  recurrence4B3A4_coeff_47
  recurrence4B3A4_coeff_48
  recurrence4B3A4_coeff_49
  recurrence4B3A4_coeff_5
  recurrence4B3A4_coeff_50
  recurrence4B3A4_coeff_51
  recurrence4B3A4_coeff_52
  recurrence4B3A4_coeff_53
  recurrence4B3A4_coeff_54
  recurrence4B3A4_coeff_55
  recurrence4B3A4_coeff_56
  recurrence4B3A4_coeff_57
  recurrence4B3A4_coeff_58
  recurrence4B3A4_coeff_59
  recurrence4B3A4_coeff_6
  recurrence4B3A4_coeff_60
  recurrence4B3A4_coeff_61
  recurrence4B3A4_coeff_62
  recurrence4B3A4_coeff_63
  recurrence4B3A4_coeff_64
  recurrence4B3A4_coeff_65
  recurrence4B3A4_coeff_66
  recurrence4B3A4_coeff_67
  recurrence4B3A4_coeff_68
  recurrence4B3A4_coeff_69
  recurrence4B3A4_coeff_7
  recurrence4B3A4_coeff_70
  recurrence4B3A4_coeff_71
  recurrence4B3A4_coeff_72
  recurrence4B3A4_coeff_73
  recurrence4B3A4_coeff_74
  recurrence4B3A4_coeff_75
  recurrence4B3A4_coeff_76
  recurrence4B3A4_coeff_77
  recurrence4B3A4_coeff_78
  recurrence4B3A4_coeff_79
  recurrence4B3A4_coeff_8
  recurrence4B3A4_coeff_80

attribute [local simp]
  recurrence4B3A4_coeff_81
  recurrence4B3A4_coeff_82
  recurrence4B3A4_coeff_83
  recurrence4B3A4_coeff_84
  recurrence4B3A4_coeff_85
  recurrence4B3A4_coeff_86
  recurrence4B3A4_coeff_87
  recurrence4B3A4_coeff_88
  recurrence4B3A4_coeff_89
  recurrence4B3A4_coeff_9
  recurrence4B3A4_coeff_90
  recurrence4B3A4_coeff_91
  recurrence4B3A4_coeff_92
  recurrence4B3A4_coeff_93
  recurrence4B3A4_coeff_94
  recurrence4B3A4_coeff_95
  recurrence4B3A4_coeff_96
  recurrence4B3A4_coeff_97
  recurrence4B3A4_coeff_98
  recurrence4B3A4_coeff_99

private theorem recurrence4Scalar2First_coeff_53_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (53 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (53 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_53 :
    recurrence4Scalar2First.coeff 53 =
      -(((1177939857635656934866474054765 * 10 ^ 70 +
        1414657380198663634455256818053292384663427512946951235659908186404935) * 10 ^ 70 +
        7843554119056088354346834304621719256404954081682997410319834224117601) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 54,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (53 - x)) = _
  rw [show 54 = 1 +
    53 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_53_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_54_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (54 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (54 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_54 :
    recurrence4Scalar2First.coeff 54 =
      (((68397774465674959877576645378900 * 10 ^ 70 +
        2465098043747384116642334264764083246009355649425212270419741856819263) * 10 ^ 70 +
        6550991011452562572677794243794115093510075896303674689598553771793065) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 55,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (54 - x)) = _
  rw [show 55 = 1 +
    54 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 22 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_54_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_55_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (55 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (55 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_55 :
    recurrence4Scalar2First.coeff 55 =
      -(((3726309046477413028410729533047701 * 10 ^ 70 +
        2694422052273393463229454345988381293783250805011273159629182886526703) * 10 ^ 70 +
        3829671735572336438004791473575998021256356428005045657895518084850932) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 56,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (55 - x)) = _
  rw [show 56 = 1 +
    55 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_55_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_56_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (56 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (56 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_56 :
    recurrence4Scalar2First.coeff 56 =
      (((190996950256374678704372733927969749 * 10 ^ 70 +
        7263921998428729561170342944334031578157109395499495755352501763983441) * 10 ^ 70 +
        2261321034703510362834152798845378771825515911315316749818651638200585) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 57,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (56 - x)) = _
  rw [show 57 = 1 +
    56 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 56 = 32 +
      24 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 24 = 24 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_56_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_57_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (57 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (57 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_57 :
    recurrence4Scalar2First.coeff 57 =
      -(((9230993608755835650674336658040949375 * 10 ^ 70 +
        1713916578545881502529162287911908032531658242734572844410229158353938) * 10 ^ 70 +
        3444461823321299176354519517509599297680286254048745355324972289054909) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 58,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (57 - x)) = _
  rw [show 58 = 1 +
    57 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_57_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_58_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (58 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (58 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_58 :
    recurrence4Scalar2First.coeff 58 =
      (((421439089723292953597642159852761720382 * 10 ^ 70 +
        6489223824172041904483359824884731049375821536563496583672066974027661) * 10 ^ 70 +
        4901435098131351261239035152753494018509628864241777398853158843045071) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 59,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (58 - x)) = _
  rw [show 59 = 1 +
    58 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 26 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_58_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_59_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (59 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (59 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_59 :
    recurrence4Scalar2First.coeff 59 =
      -(((18202733858100599637431053158560692080509 * 10 ^ 70 +
        0150517672514375633274610038373077201329668059149661424774527655596253) * 10 ^ 70 +
        6071413179465262246176193794645610318704668478497124837960813897989070) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 60,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (59 - x)) = _
  rw [show 60 = 1 +
    59 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_59_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_60_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (60 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (60 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_60 :
    recurrence4Scalar2First.coeff 60 =
      (((744712150087788399952458167204864528759463 * 10 ^ 70 +
        3449771417287204963442455904949553180591219490026119126224079684497472) * 10 ^ 70 +
        6405549365455737670241208482896632301748685487418931323891011827981402) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 61,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (60 - x)) = _
  rw [show 61 = 1 +
    60 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 60 = 32 +
      28 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 28 = 28 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_60_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_61_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (61 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (61 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_61 :
    recurrence4Scalar2First.coeff 61 =
      -(((28888278974305752875770806428212773801827630 * 10 ^ 70 +
        1473731837011187534389631194709181316150052731650965782223800318302971) * 10 ^ 70 +
        1344878954403683041714344469125458617412542021734509260080529168142068) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 62,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (61 - x)) = _
  rw [show 62 = 1 +
    61 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 61 = 32 +
      29 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 29 = 29 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_61_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_62_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (62 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (62 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_62 :
    recurrence4Scalar2First.coeff 62 =
      (((1063337051891257868116392246800276365600821276 * 10 ^ 70 +
        9738604974485768964444636245886435683795072152874817899852707499927204) * 10 ^ 70 +
        7682745001876329876934343412591277476260181678476209849235482258856480) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 63,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (62 - x)) = _
  rw [show 63 = 1 +
    62 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 62 = 32 +
      30 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 30 = 30 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_62_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_63_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (63 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (63 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_63 :
    recurrence4Scalar2First.coeff 63 =
      -(((37159900058414243115683402258817848503739700667 * 10 ^ 70 +
        1748280759911816855563298554616239160800123346296066668785121790607583) * 10 ^ 70 +
        7705590042129868915673744038318478818910597971203840579897059145388591) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 64,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (63 - x)) = _
  rw [show 64 = 1 +
    63 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 31 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_63_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_64_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (64 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (64 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_64 :
    recurrence4Scalar2First.coeff 64 =
      (((1233299561814208629985835918077475091784555876092 * 10 ^ 70 +
        9502933992782982675374362567787022395055478337754408678686924719764097) * 10 ^ 70 +
        8730389143898297312998118519669335748022679235515510020329914728165631) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 65,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (64 - x)) = _
  rw [show 65 = 1 +
    64 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_64_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_65_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (65 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (65 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_65 :
    recurrence4Scalar2First.coeff 65 =
      -(((38875331571707598739104492646816845768231983632084 * 10 ^ 70 +
        5850759771969309879401854482466226428334783598250379128866738822575159) * 10 ^ 70 +
        0411673443243375035772132805659259865781369735251411746550354627012894) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 66,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (65 - x)) = _
  rw [show 66 = 1 +
    65 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 65 = 32 +
      33 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 33 = 32 +
      1 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 1 = 1 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_65_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_66_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (66 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (66 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_66 :
    recurrence4Scalar2First.coeff 66 =
      (((1163521701454956177351801806732299331163733049787933 * 10 ^ 70 +
        3082195699248696007283902672502326955605423264220926803523061689995347) * 10 ^ 70 +
        1668600485697298852233720371904477153993196548209249794837352911184263) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 67,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (66 - x)) = _
  rw [show 67 = 1 +
    66 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 66 = 32 +
      34 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 34 = 32 +
      2 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 2 = 2 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_66_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_67_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (67 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (67 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_67 :
    recurrence4Scalar2First.coeff 67 =
      -(((33042944778058708146155761787525516863081200795457833 * 10 ^ 70 +
        8970398308784610428892954197464106866480141954275778366036854097757432) * 10 ^ 70 +
        6412735881917907975230793202667409546951978901929480855837704641867736) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 68,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (67 - x)) = _
  rw [show 68 = 1 +
    67 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_67_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_68_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (68 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (68 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_68 :
    recurrence4Scalar2First.coeff 68 =
      (((889329294568563889236792537009958464164201537136531226 * 10 ^ 70 +
        9545109920066391379190186956916211710969392822964133634395373692574234) * 10 ^ 70 +
        4117281984010521222186392408295202241420795553619791870153332114557465) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 69,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (68 - x)) = _
  rw [show 69 = 1 +
    68 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 68 = 32 +
      36 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 36 = 32 +
      4 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_68_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_69_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (69 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (69 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_69 :
    recurrence4Scalar2First.coeff 69 =
      -(((22639758785593991448026292981625583845938433221983090581 * 10 ^ 70 +
        8763821847683839968433606631738984663457186106283136313795499500893615) * 10 ^ 70 +
        4014508886915818306418649696140266862916998321768470862136710824122991) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 70,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (69 - x)) = _
  rw [show 70 = 1 +
    69 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 32 +
      5 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 5 = 5 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_69_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_70_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (70 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (70 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_70 :
    recurrence4Scalar2First.coeff 70 =
      (((543446948095094110205603721599711801828994263409928063539 * 10 ^ 70 +
        4786933512742306851110524328609169296681535172561799039402853764351061) * 10 ^ 70 +
        7613917212891633798814350042115554351090896597426247125405220200889884) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 71,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (70 - x)) = _
  rw [show 71 = 1 +
    70 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 70 = 32 +
      38 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 38 = 32 +
      6 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 6 = 6 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_70_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_71_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (71 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (71 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_71 :
    recurrence4Scalar2First.coeff 71 =
      -(((12239852688464006012804400376312207781079524840430017839900 * 10 ^ 70 +
        2411412086908766789272020451125088417393710033471153782310968086356252) * 10 ^ 70 +
        7789231248113783547614541648205935432023359684341282053275816673796644) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 72,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (71 - x)) = _
  rw [show 72 = 1 +
    71 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 71 = 32 +
      39 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 39 = 32 +
      7 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_71_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_72_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (72 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (72 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_72 :
    recurrence4Scalar2First.coeff 72 =
      (((256571441114951213068949222989713422664675858678164036899041 * 10 ^ 70 +
        9998609530791965056051681765407401555060601670615773420031205629793605) * 10 ^ 70 +
        5258728782036683908101305004496136928522188038030105531368733597845305) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 73,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (72 - x)) = _
  rw [show 73 = 1 +
    72 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 72 = 32 +
      40 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 40 = 32 +
      8 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 8 = 8 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_72_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_73_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (73 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (73 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_73 :
    recurrence4Scalar2First.coeff 73 =
      -(((4934853305384518853569652585757152724189970171146272780152222 * 10 ^ 70 +
        1576127121255145376082949637873600446086426286826138671034891835795953) * 10 ^ 70 +
        9290888588024949544106749845171361699606504027120703948261656339589606) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 74,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (73 - x)) = _
  rw [show 74 = 1 +
    73 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 73 = 32 +
      41 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 41 = 32 +
      9 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 9 = 9 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_73_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_74_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (74 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (74 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_74 :
    recurrence4Scalar2First.coeff 74 =
      (((84692222225171974084582088356542527563790887216565690938220853 * 10 ^ 70 +
        9883020362525945381637669889000610677225996937111748900922825676560854) * 10 ^ 70 +
        8507767454921109522833378642430224345305721656956497872899540939338934) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 75,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (74 - x)) = _
  rw [show 75 = 1 +
    74 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 74 = 32 +
      42 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 42 = 32 +
      10 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 10 = 10 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_74_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_75_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (75 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (75 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_75 :
    recurrence4Scalar2First.coeff 75 =
      -(((1213085990140362813340959637725861265420696114179814124039290645 * 10 ^ 70 +
        6290977866412024675057029778796480749750962126091900791615092802659277) * 10 ^ 70 +
        0976675159620385682608441959315375822376571808853131475622856385320123) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 76,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (75 - x)) = _
  rw [show 76 = 1 +
    75 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 75 = 32 +
      43 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 43 = 32 +
      11 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 11 = 11 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_75_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_76_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (76 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (76 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_76 :
    recurrence4Scalar2First.coeff 76 =
      (((11341585506321966061087592217647844171388546103657452341777386014 * 10 ^ 70 +
        6691005237488392830363371117182726091239814551441821205839402680106108) * 10 ^ 70 +
        8508020373128430178831287943356556203168724472990349271112635096138896) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 77,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (76 - x)) = _
  rw [show 77 = 1 +
    76 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 76 = 32 +
      44 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 44 = 32 +
      12 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 12 = 12 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_76_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_77_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (77 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (77 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_77 :
    recurrence4Scalar2First.coeff 77 =
      (((70627686042813309296036128577478657702206047440083686902394498206 * 10 ^ 70 +
        7586224520704712018529947770324281365013464900737464782898942883738142) * 10 ^ 70 +
        7806801212672024725480330989047762261832808739041699880011404546684257) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 78,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (77 - x)) = _
  rw [show 78 = 1 +
    77 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 77 = 32 +
      45 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_77_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_78_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (78 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (78 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_78 :
    recurrence4Scalar2First.coeff 78 =
      -(((7426965143966340271903605090385440064179773412163345804309319237199 * 10 ^ 70 +
        1625629930037819598770890898476694161358242403495208844097835175890550) * 10 ^ 70 +
        7206831287190769839771857745969139542382435438929445791450644700752214) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 79,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (78 - x)) = _
  rw [show 79 = 1 +
    78 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 78 = 32 +
      46 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 46 = 32 +
      14 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_78_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_79_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (79 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (79 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_79 :
    recurrence4Scalar2First.coeff 79 =
      (((254901613128399835313944612615168227357735641083678194506889531822399 * 10 ^ 70 +
        6470776876151910510385079206178142467781903665374863137977541302102822) * 10 ^ 70 +
        0579381939060602958406833424433257486392955423632961487886435858434231) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 80,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (79 - x)) = _
  rw [show 80 = 1 +
    79 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 79 = 32 +
      47 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 47 = 32 +
      15 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_79_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_80_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (80 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (80 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_80 :
    recurrence4Scalar2First.coeff 80 =
      -(((6682032314807883436664827986298510924153638934731100837162745262958419 * 10 ^ 70 +
        0329046568340264936337623437565512794492751699938828232096478727463901) * 10 ^ 70 +
        3150508068030863884041157534835786416539106293352712455635623061476706) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 81,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (80 - x)) = _
  rw [show 81 = 1 +
    80 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 80 = 32 +
      48 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 48 = 32 +
      16 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 16 = 16 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_80_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_81_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (81 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (81 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_81 :
    recurrence4Scalar2First.coeff 81 =
      ((((15 * 10 ^ 70 +
        0954763950007491031680715168792879708525236546679143000479731159112256) * 10 ^ 70 +
        6756973046992019728628151746757781024192581332548325840747285649954786) * 10 ^ 70 +
        7170559979736733333372512816995048041851207337663905219330839179880490) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 82,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (81 - x)) = _
  rw [show 82 = 1 +
    81 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_81_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_82_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (82 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (82 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_82 :
    recurrence4Scalar2First.coeff 82 =
      -((((305 * 10 ^ 70 +
        5579088689530356838864305616395977607777075826302993741295629666503400) * 10 ^ 70 +
        7645875598616257678766893188492872686263439705973924622252733817876656) * 10 ^ 70 +
        5461609595002573986012758905948499744050478460499286769581258989376956) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 83,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (82 - x)) = _
  rw [show 83 = 1 +
    82 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_82_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_83_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (83 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (83 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_83 :
    recurrence4Scalar2First.coeff 83 =
      ((((5616 * 10 ^ 70 +
        4890548677659051507383925808185022343761638136895564574721988994767921) * 10 ^ 70 +
        8387409873103077606547871487479562354440998269201014225180850836002089) * 10 ^ 70 +
        2367535900222690799945267768723606970757003436473624858444084955497236) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 84,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (83 - x)) = _
  rw [show 84 = 1 +
    83 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_83_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_84_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (84 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (84 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_84 :
    recurrence4Scalar2First.coeff 84 =
      -((((93691 * 10 ^ 70 +
        0139033089046993438814706021554573088928768475962380066812109484393032) * 10 ^ 70 +
        2126214459435113116747101260857092244481969801325878368062427432590658) * 10 ^ 70 +
        6545496666015221409895451370790470263045266909738378822764805445860805) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 85,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (84 - x)) = _
  rw [show 85 = 1 +
    84 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 84 = 32 +
      52 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 52 = 32 +
      20 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 20 = 20 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_84_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_85_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (85 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (85 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_85 :
    recurrence4Scalar2First.coeff 85 =
      ((((1396657 * 10 ^ 70 +
        8908670127185420100726168026091576207244494644219714422235345777407242) * 10 ^ 70 +
        4636649058094290830409738518843165043419450783391306875398573968400279) * 10 ^ 70 +
        9780309824110470195347232311907425023669132884185336320452401789437470) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 86,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (85 - x)) = _
  rw [show 86 = 1 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_85_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_86_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (86 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (86 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_86 :
    recurrence4Scalar2First.coeff 86 =
      -((((17782627 * 10 ^ 70 +
        3382094662238924851480899405407165550283143324452478197730367683935470) * 10 ^ 70 +
        3946442094362617326575896847010686849511711696310618212843534588015632) * 10 ^ 70 +
        0064317820769830138954666989972172015864715761731131399356988373476091) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 87,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (86 - x)) = _
  rw [show 87 = 1 +
    86 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 22 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_86_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_87_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (87 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (87 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_87 :
    recurrence4Scalar2First.coeff 87 =
      ((((166261003 * 10 ^ 70 +
        3152771871936109046424736698903726149823117108298110447868465558848743) * 10 ^ 70 +
        8891771506717936137739347476563152697486250038315584976024291673757060) * 10 ^ 70 +
        9630767096820872611327817010873301542367082210160293121946818964199064) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 88,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (87 - x)) = _
  rw [show 88 = 1 +
    87 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_87_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_88_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (88 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (88 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_88 :
    recurrence4Scalar2First.coeff 88 =
      -((((177984509 * 10 ^ 70 +
        7316654714756783718923603943114240587347391012190317016424356352358965) * 10 ^ 70 +
        9257349474857118596473836267893852700120287452238539232816853811239849) * 10 ^ 70 +
        6328275619327931647013094435297395409322003961751629077249320464253096) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 89,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (88 - x)) = _
  rw [show 89 = 1 +
    88 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 88 = 32 +
      56 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 56 = 32 +
      24 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 24 = 24 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_88_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_89_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (89 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (89 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_89 :
    recurrence4Scalar2First.coeff 89 =
      -((((42696901957 * 10 ^ 70 +
        0092561282586221850921808904056147629194992945004711943744862050165947) * 10 ^ 70 +
        9807328656052640706214888674074531878984246032933279062246671613331748) * 10 ^ 70 +
        3487082185622755002727776206404709221070293193225270534340124603196615) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 90,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (89 - x)) = _
  rw [show 90 = 1 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_89_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_90_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (90 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (90 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_90 :
    recurrence4Scalar2First.coeff 90 =
      ((((1432883111751 * 10 ^ 70 +
        7046499338513372139304312293312885106111474338699435428539203233121119) * 10 ^ 70 +
        0540793940155033981920596808785691026245708194286560459010921885744253) * 10 ^ 70 +
        2936747631137457207365583088603080272953801208831038889587103726702865) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 91,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (90 - x)) = _
  rw [show 91 = 1 +
    90 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 26 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_90_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_91_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (91 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (91 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_91 :
    recurrence4Scalar2First.coeff 91 =
      -((((34058263442227 * 10 ^ 70 +
        2442319297421609201541791197855565198918072831192715199816688091968064) * 10 ^ 70 +
        8925227247002350920956471176328875462366956845564729350109178150884702) * 10 ^ 70 +
        8943854081572142770446548091457756540982241027198122316773374617133551) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 92,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (91 - x)) = _
  rw [show 92 = 1 +
    91 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 91 = 32 +
      59 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_91_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_92_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (92 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (92 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_92 :
    recurrence4Scalar2First.coeff 92 =
      ((((692364215552344 * 10 ^ 70 +
        4663439447120087172224153412346580008090331644897209408463187111130442) * 10 ^ 70 +
        3480942685451550023157167726789252169666216595228219037580376867957656) * 10 ^ 70 +
        1535361938428254010866393597427828027912677790748372573882736172794340) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 93,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (92 - x)) = _
  rw [show 93 = 1 +
    92 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 92 = 32 +
      60 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 60 = 32 +
      28 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 28 = 28 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_92_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_93_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (93 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (93 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_93 :
    recurrence4Scalar2First.coeff 93 =
      -((((12752108709087567 * 10 ^ 70 +
        0029924144488550675263861940792389275024936593441107503306106513607870) * 10 ^ 70 +
        9338989753505540146672497575637146216986153594012147928212209985870610) * 10 ^ 70 +
        2554784607767811324895061678158025584860233152040809093076554604802707) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 94,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (93 - x)) = _
  rw [show 94 = 1 +
    93 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 93 = 32 +
      61 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 61 = 32 +
      29 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 29 = 29 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_93_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_94_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (94 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (94 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_94 :
    recurrence4Scalar2First.coeff 94 =
      ((((218337659877707388 * 10 ^ 70 +
        2594379115995791963221084809791325332245709010152008593499451492149032) * 10 ^ 70 +
        8628516169299768162361047805319740803088912117324795573066984429653680) * 10 ^ 70 +
        2689071888863733293990509636688869737091475568149037153257175567776022) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 95,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (94 - x)) = _
  rw [show 95 = 1 +
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
  rw [recurrence4Scalar2First_coeff_94_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_95_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (95 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (95 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_95 :
    recurrence4Scalar2First.coeff 95 =
      -((((3523793462810947163 * 10 ^ 70 +
        8515440373184650373154414294205662557867215125093142736635227141207696) * 10 ^ 70 +
        1195186931590605532709628491476472345712562337257173258388200778609493) * 10 ^ 70 +
        4066387653235773906876370235173226290010757170472122539176378150892955) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 96,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (95 - x)) = _
  rw [show 96 = 1 +
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
  rw [recurrence4Scalar2First_coeff_95_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_96_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (96 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (96 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_96 :
    recurrence4Scalar2First.coeff 96 =
      ((((54064294951039715430 * 10 ^ 70 +
        3858470490135770202746758026055153690669954443600433692493359697848531) * 10 ^ 70 +
        0089552157605084062577520552493786030613084257134016863794670266316742) * 10 ^ 70 +
        7679874030129888630490127864926916073369932196310540180240003434941124) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 97,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (96 - x)) = _
  rw [show 97 = 1 +
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
  rw [recurrence4Scalar2First_coeff_96_prefix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
