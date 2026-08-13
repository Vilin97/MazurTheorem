/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupLeadingSquare
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupA1
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar1LeftPart0Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar1Left coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4A1_coeff_1
  recurrence4A1_coeff_10
  recurrence4A1_coeff_100
  recurrence4A1_coeff_101
  recurrence4A1_coeff_102
  recurrence4A1_coeff_103
  recurrence4A1_coeff_104
  recurrence4A1_coeff_105
  recurrence4A1_coeff_106
  recurrence4A1_coeff_107
  recurrence4A1_coeff_108
  recurrence4A1_coeff_109
  recurrence4A1_coeff_11
  recurrence4A1_coeff_110
  recurrence4A1_coeff_111
  recurrence4A1_coeff_112
  recurrence4A1_coeff_113
  recurrence4A1_coeff_114
  recurrence4A1_coeff_115
  recurrence4A1_coeff_116
  recurrence4A1_coeff_117
  recurrence4A1_coeff_118
  recurrence4A1_coeff_119
  recurrence4A1_coeff_12
  recurrence4A1_coeff_120
  recurrence4A1_coeff_121
  recurrence4A1_coeff_122
  recurrence4A1_coeff_123
  recurrence4A1_coeff_124
  recurrence4A1_coeff_125
  recurrence4A1_coeff_126
  recurrence4A1_coeff_127
  recurrence4A1_coeff_128
  recurrence4A1_coeff_129
  recurrence4A1_coeff_13
  recurrence4A1_coeff_130
  recurrence4A1_coeff_131
  recurrence4A1_coeff_132
  recurrence4A1_coeff_133
  recurrence4A1_coeff_134
  recurrence4A1_coeff_135
  recurrence4A1_coeff_136
  recurrence4A1_coeff_137
  recurrence4A1_coeff_138
  recurrence4A1_coeff_139
  recurrence4A1_coeff_14
  recurrence4A1_coeff_140
  recurrence4A1_coeff_141
  recurrence4A1_coeff_142
  recurrence4A1_coeff_143
  recurrence4A1_coeff_144
  recurrence4A1_coeff_145
  recurrence4A1_coeff_146
  recurrence4A1_coeff_147
  recurrence4A1_coeff_148
  recurrence4A1_coeff_149
  recurrence4A1_coeff_15
  recurrence4A1_coeff_150
  recurrence4A1_coeff_151
  recurrence4A1_coeff_152
  recurrence4A1_coeff_153
  recurrence4A1_coeff_154
  recurrence4A1_coeff_155
  recurrence4A1_coeff_156

attribute [local simp]
  recurrence4A1_coeff_157
  recurrence4A1_coeff_158
  recurrence4A1_coeff_159
  recurrence4A1_coeff_16
  recurrence4A1_coeff_160
  recurrence4A1_coeff_161
  recurrence4A1_coeff_162
  recurrence4A1_coeff_17
  recurrence4A1_coeff_18
  recurrence4A1_coeff_19
  recurrence4A1_coeff_2
  recurrence4A1_coeff_20
  recurrence4A1_coeff_21
  recurrence4A1_coeff_22
  recurrence4A1_coeff_23
  recurrence4A1_coeff_24
  recurrence4A1_coeff_25
  recurrence4A1_coeff_26
  recurrence4A1_coeff_27
  recurrence4A1_coeff_28
  recurrence4A1_coeff_29
  recurrence4A1_coeff_3
  recurrence4A1_coeff_30
  recurrence4A1_coeff_31
  recurrence4A1_coeff_32
  recurrence4A1_coeff_33
  recurrence4A1_coeff_34
  recurrence4A1_coeff_35
  recurrence4A1_coeff_36
  recurrence4A1_coeff_37
  recurrence4A1_coeff_38
  recurrence4A1_coeff_39
  recurrence4A1_coeff_4
  recurrence4A1_coeff_40
  recurrence4A1_coeff_41
  recurrence4A1_coeff_42
  recurrence4A1_coeff_43
  recurrence4A1_coeff_44
  recurrence4A1_coeff_45
  recurrence4A1_coeff_46
  recurrence4A1_coeff_47
  recurrence4A1_coeff_48
  recurrence4A1_coeff_49
  recurrence4A1_coeff_5
  recurrence4A1_coeff_50
  recurrence4A1_coeff_51
  recurrence4A1_coeff_52
  recurrence4A1_coeff_53
  recurrence4A1_coeff_54
  recurrence4A1_coeff_55
  recurrence4A1_coeff_56
  recurrence4A1_coeff_57
  recurrence4A1_coeff_58
  recurrence4A1_coeff_59
  recurrence4A1_coeff_6
  recurrence4A1_coeff_60
  recurrence4A1_coeff_61
  recurrence4A1_coeff_62
  recurrence4A1_coeff_63
  recurrence4A1_coeff_64
  recurrence4A1_coeff_65
  recurrence4A1_coeff_66
  recurrence4A1_coeff_67
  recurrence4A1_coeff_68

attribute [local simp]
  recurrence4A1_coeff_69
  recurrence4A1_coeff_7
  recurrence4A1_coeff_70
  recurrence4A1_coeff_71
  recurrence4A1_coeff_72
  recurrence4A1_coeff_73
  recurrence4A1_coeff_74
  recurrence4A1_coeff_75
  recurrence4A1_coeff_76
  recurrence4A1_coeff_77
  recurrence4A1_coeff_78
  recurrence4A1_coeff_79
  recurrence4A1_coeff_8
  recurrence4A1_coeff_80
  recurrence4A1_coeff_81
  recurrence4A1_coeff_82
  recurrence4A1_coeff_83
  recurrence4A1_coeff_84
  recurrence4A1_coeff_85
  recurrence4A1_coeff_86
  recurrence4A1_coeff_87
  recurrence4A1_coeff_88
  recurrence4A1_coeff_89
  recurrence4A1_coeff_9
  recurrence4A1_coeff_90
  recurrence4A1_coeff_91
  recurrence4A1_coeff_92
  recurrence4A1_coeff_93
  recurrence4A1_coeff_94
  recurrence4A1_coeff_95
  recurrence4A1_coeff_96
  recurrence4A1_coeff_97
  recurrence4A1_coeff_98
  recurrence4A1_coeff_99
  recurrence4LeadingSquare_coeff_0
  recurrence4LeadingSquare_coeff_1
  recurrence4LeadingSquare_coeff_10
  recurrence4LeadingSquare_coeff_100
  recurrence4LeadingSquare_coeff_101
  recurrence4LeadingSquare_coeff_102
  recurrence4LeadingSquare_coeff_103
  recurrence4LeadingSquare_coeff_104
  recurrence4LeadingSquare_coeff_105
  recurrence4LeadingSquare_coeff_106
  recurrence4LeadingSquare_coeff_107
  recurrence4LeadingSquare_coeff_108
  recurrence4LeadingSquare_coeff_109
  recurrence4LeadingSquare_coeff_11
  recurrence4LeadingSquare_coeff_110
  recurrence4LeadingSquare_coeff_111
  recurrence4LeadingSquare_coeff_112
  recurrence4LeadingSquare_coeff_113
  recurrence4LeadingSquare_coeff_114
  recurrence4LeadingSquare_coeff_115
  recurrence4LeadingSquare_coeff_116
  recurrence4LeadingSquare_coeff_117
  recurrence4LeadingSquare_coeff_118
  recurrence4LeadingSquare_coeff_119
  recurrence4LeadingSquare_coeff_12
  recurrence4LeadingSquare_coeff_120
  recurrence4LeadingSquare_coeff_121
  recurrence4LeadingSquare_coeff_122
  recurrence4LeadingSquare_coeff_123
  recurrence4LeadingSquare_coeff_124

attribute [local simp]
  recurrence4LeadingSquare_coeff_125
  recurrence4LeadingSquare_coeff_126
  recurrence4LeadingSquare_coeff_127
  recurrence4LeadingSquare_coeff_128
  recurrence4LeadingSquare_coeff_129
  recurrence4LeadingSquare_coeff_13
  recurrence4LeadingSquare_coeff_130
  recurrence4LeadingSquare_coeff_131
  recurrence4LeadingSquare_coeff_132
  recurrence4LeadingSquare_coeff_133
  recurrence4LeadingSquare_coeff_134
  recurrence4LeadingSquare_coeff_135
  recurrence4LeadingSquare_coeff_136
  recurrence4LeadingSquare_coeff_137
  recurrence4LeadingSquare_coeff_138
  recurrence4LeadingSquare_coeff_139
  recurrence4LeadingSquare_coeff_14
  recurrence4LeadingSquare_coeff_140
  recurrence4LeadingSquare_coeff_141
  recurrence4LeadingSquare_coeff_142
  recurrence4LeadingSquare_coeff_143
  recurrence4LeadingSquare_coeff_144
  recurrence4LeadingSquare_coeff_145
  recurrence4LeadingSquare_coeff_146
  recurrence4LeadingSquare_coeff_147
  recurrence4LeadingSquare_coeff_148
  recurrence4LeadingSquare_coeff_149
  recurrence4LeadingSquare_coeff_15
  recurrence4LeadingSquare_coeff_150
  recurrence4LeadingSquare_coeff_151
  recurrence4LeadingSquare_coeff_152
  recurrence4LeadingSquare_coeff_153
  recurrence4LeadingSquare_coeff_154
  recurrence4LeadingSquare_coeff_155
  recurrence4LeadingSquare_coeff_156
  recurrence4LeadingSquare_coeff_157
  recurrence4LeadingSquare_coeff_158
  recurrence4LeadingSquare_coeff_159
  recurrence4LeadingSquare_coeff_16
  recurrence4LeadingSquare_coeff_160
  recurrence4LeadingSquare_coeff_161
  recurrence4LeadingSquare_coeff_17
  recurrence4LeadingSquare_coeff_18
  recurrence4LeadingSquare_coeff_19
  recurrence4LeadingSquare_coeff_2
  recurrence4LeadingSquare_coeff_20
  recurrence4LeadingSquare_coeff_21
  recurrence4LeadingSquare_coeff_22
  recurrence4LeadingSquare_coeff_23
  recurrence4LeadingSquare_coeff_24
  recurrence4LeadingSquare_coeff_25
  recurrence4LeadingSquare_coeff_26
  recurrence4LeadingSquare_coeff_27
  recurrence4LeadingSquare_coeff_28
  recurrence4LeadingSquare_coeff_29
  recurrence4LeadingSquare_coeff_3
  recurrence4LeadingSquare_coeff_30
  recurrence4LeadingSquare_coeff_31
  recurrence4LeadingSquare_coeff_32
  recurrence4LeadingSquare_coeff_33
  recurrence4LeadingSquare_coeff_34
  recurrence4LeadingSquare_coeff_35
  recurrence4LeadingSquare_coeff_36
  recurrence4LeadingSquare_coeff_37

attribute [local simp]
  recurrence4LeadingSquare_coeff_38
  recurrence4LeadingSquare_coeff_39
  recurrence4LeadingSquare_coeff_4
  recurrence4LeadingSquare_coeff_40
  recurrence4LeadingSquare_coeff_41
  recurrence4LeadingSquare_coeff_42
  recurrence4LeadingSquare_coeff_43
  recurrence4LeadingSquare_coeff_44
  recurrence4LeadingSquare_coeff_45
  recurrence4LeadingSquare_coeff_46
  recurrence4LeadingSquare_coeff_47
  recurrence4LeadingSquare_coeff_48
  recurrence4LeadingSquare_coeff_49
  recurrence4LeadingSquare_coeff_5
  recurrence4LeadingSquare_coeff_50
  recurrence4LeadingSquare_coeff_51
  recurrence4LeadingSquare_coeff_52
  recurrence4LeadingSquare_coeff_53
  recurrence4LeadingSquare_coeff_54
  recurrence4LeadingSquare_coeff_55
  recurrence4LeadingSquare_coeff_56
  recurrence4LeadingSquare_coeff_57
  recurrence4LeadingSquare_coeff_58
  recurrence4LeadingSquare_coeff_59
  recurrence4LeadingSquare_coeff_6
  recurrence4LeadingSquare_coeff_60
  recurrence4LeadingSquare_coeff_61
  recurrence4LeadingSquare_coeff_62
  recurrence4LeadingSquare_coeff_63
  recurrence4LeadingSquare_coeff_64
  recurrence4LeadingSquare_coeff_65
  recurrence4LeadingSquare_coeff_66
  recurrence4LeadingSquare_coeff_67
  recurrence4LeadingSquare_coeff_68
  recurrence4LeadingSquare_coeff_69
  recurrence4LeadingSquare_coeff_7
  recurrence4LeadingSquare_coeff_70
  recurrence4LeadingSquare_coeff_71
  recurrence4LeadingSquare_coeff_72
  recurrence4LeadingSquare_coeff_73
  recurrence4LeadingSquare_coeff_74
  recurrence4LeadingSquare_coeff_75
  recurrence4LeadingSquare_coeff_76
  recurrence4LeadingSquare_coeff_77
  recurrence4LeadingSquare_coeff_78
  recurrence4LeadingSquare_coeff_79
  recurrence4LeadingSquare_coeff_8
  recurrence4LeadingSquare_coeff_80
  recurrence4LeadingSquare_coeff_81
  recurrence4LeadingSquare_coeff_82
  recurrence4LeadingSquare_coeff_83
  recurrence4LeadingSquare_coeff_84
  recurrence4LeadingSquare_coeff_85
  recurrence4LeadingSquare_coeff_86
  recurrence4LeadingSquare_coeff_87
  recurrence4LeadingSquare_coeff_88
  recurrence4LeadingSquare_coeff_89
  recurrence4LeadingSquare_coeff_9
  recurrence4LeadingSquare_coeff_90
  recurrence4LeadingSquare_coeff_91
  recurrence4LeadingSquare_coeff_92
  recurrence4LeadingSquare_coeff_93
  recurrence4LeadingSquare_coeff_94
  recurrence4LeadingSquare_coeff_95

attribute [local simp]
  recurrence4LeadingSquare_coeff_96
  recurrence4LeadingSquare_coeff_97
  recurrence4LeadingSquare_coeff_98
  recurrence4LeadingSquare_coeff_99

private theorem recurrence4Scalar1Left_coeff_41_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (41 + x) *
        remainder4Coefficient1.coeff (41 - (41 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 41 + x
  · rw [recurrence4LeadingSquare_coeff_high (41 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (41 - (41 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_41 :
    recurrence4Scalar1Left.coeff 41 =
      (((1148846 * 10 ^ 70 +
        1626572250667005079425759856297232727257996451614468228865094920222026) * 10 ^ 70 +
        3792495794554404785681662751583174858064112866812140091935480513022931) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 42,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (41 - x)) = _
  rw [show 42 = 0 +
    42 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 42 = 32 +
      10 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 10 = 9 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_41_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_42_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (42 + x) *
        remainder4Coefficient1.coeff (42 - (42 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 42 + x
  · rw [recurrence4LeadingSquare_coeff_high (42 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (42 - (42 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_42 :
    recurrence4Scalar1Left.coeff 42 =
      -(((124308326 * 10 ^ 70 +
        3221735196797081044441833709157382764775843958464065854995075992914235) * 10 ^ 70 +
        0010252046830046343361212501601916422917948223909433562945445174033837) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 43,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (42 - x)) = _
  rw [show 43 = 0 +
    43 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 43 = 32 +
      11 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 11 = 10 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_42_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_43_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (43 + x) *
        remainder4Coefficient1.coeff (43 - (43 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 43 + x
  · rw [recurrence4LeadingSquare_coeff_high (43 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (43 - (43 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_43 :
    recurrence4Scalar1Left.coeff 43 =
      (((10913350609 * 10 ^ 70 +
        3225905214195092533048606518572526601835524101804677867375848131920922) * 10 ^ 70 +
        2969121297382274173820844489849694431048179651609709824595325739709436) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 44,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (43 - x)) = _
  rw [show 44 = 0 +
    44 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 44 = 32 +
      12 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 12 = 11 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_43_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_44_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (44 + x) *
        remainder4Coefficient1.coeff (44 - (44 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 44 + x
  · rw [recurrence4LeadingSquare_coeff_high (44 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (44 - (44 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_44 :
    recurrence4Scalar1Left.coeff 44 =
      -(((739332237013 * 10 ^ 70 +
        7504607518401542299917024329655125842142354044791876901123928470328442) * 10 ^ 70 +
        8075615207926955139669317154830048393559817964842013129583655107410632) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 45,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (44 - x)) = _
  rw [show 45 = 0 +
    45 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 12 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_44_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_45_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (45 + x) *
        remainder4Coefficient1.coeff (45 - (45 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 45 + x
  · rw [recurrence4LeadingSquare_coeff_high (45 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (45 - (45 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_45 :
    recurrence4Scalar1Left.coeff 45 =
      (((28902952590510 * 10 ^ 70 +
        5214474693553824868924779110769165782742141414723386825438643958872162) * 10 ^ 70 +
        0772477451838890395178278622616462989142547151883703274294522444572154) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 46,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (45 - x)) = _
  rw [show 46 = 0 +
    46 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 46 = 32 +
      14 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 14 = 13 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_45_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_46_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (46 + x) *
        remainder4Coefficient1.coeff (46 - (46 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 46 + x
  · rw [recurrence4LeadingSquare_coeff_high (46 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (46 - (46 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_46 :
    recurrence4Scalar1Left.coeff 46 =
      (((1433083287659396 * 10 ^ 70 +
        5182620558734669929277434720698797523685607495836743829463563897269255) * 10 ^ 70 +
        5592188378715877942958035305732199235488182575508901428184224619185139) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 47,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (46 - x)) = _
  rw [show 47 = 0 +
    47 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 47 = 32 +
      15 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 15 = 14 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_46_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_47_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (47 + x) *
        remainder4Coefficient1.coeff (47 - (47 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 47 + x
  · rw [recurrence4LeadingSquare_coeff_high (47 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (47 - (47 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_47 :
    recurrence4Scalar1Left.coeff 47 =
      -(((467825012025360587 * 10 ^ 70 +
        1229019258667720152222877242863814248283457028901049268262574229044204) * 10 ^ 70 +
        2911267944771046770336243144437473159491353247110663938414554785326295) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 48,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (47 - x)) = _
  rw [show 48 = 0 +
    48 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 48 = 32 +
      16 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 16 = 15 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_47_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_48_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (48 + x) *
        remainder4Coefficient1.coeff (48 - (48 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 48 + x
  · rw [recurrence4LeadingSquare_coeff_high (48 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (48 - (48 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_48 :
    recurrence4Scalar1Left.coeff 48 =
      (((64357831141051309904 * 10 ^ 70 +
        7550022315575286603205434792065644540527317658217170067568085056690785) * 10 ^ 70 +
        8593564258855357598288974834245892632080546773583592928303714330123153) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 49,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (48 - x)) = _
  rw [show 49 = 0 +
    49 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 16 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_48_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_49_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (49 + x) *
        remainder4Coefficient1.coeff (49 - (49 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 49 + x
  · rw [recurrence4LeadingSquare_coeff_high (49 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (49 - (49 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_49 :
    recurrence4Scalar1Left.coeff 49 =
      -(((6780283266861045609800 * 10 ^ 70 +
        7146285368243627927768157052128879010501561634520113784553497703404740) * 10 ^ 70 +
        5692723102804397706380259354327566626733494837786774798519315844539137) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 50,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (49 - x)) = _
  rw [show 50 = 0 +
    50 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 17 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_49_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_50_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (50 + x) *
        remainder4Coefficient1.coeff (50 - (50 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 50 + x
  · rw [recurrence4LeadingSquare_coeff_high (50 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (50 - (50 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_50 :
    recurrence4Scalar1Left.coeff 50 =
      (((610168502147786387417529 * 10 ^ 70 +
        3610903284770278198739749426641189494694081413204614037087598518002998) * 10 ^ 70 +
        6814344214990134625063780258654579733723893496350998192641617502700328) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 51,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (50 - x)) = _
  rw [show 51 = 0 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 18 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_50_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_51_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (51 + x) *
        remainder4Coefficient1.coeff (51 - (51 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 51 + x
  · rw [recurrence4LeadingSquare_coeff_high (51 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (51 - (51 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_51 :
    recurrence4Scalar1Left.coeff 51 =
      -(((48887946504534378661299359 * 10 ^ 70 +
        4375449768558053770594703440818438198096539657645964227289110978414487) * 10 ^ 70 +
        4905676138968354679254882647990583976697812655438731515697504218436751) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 52,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (51 - x)) = _
  rw [show 52 = 0 +
    52 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 52 = 32 +
      20 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 20 = 19 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_51_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_52_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (52 + x) *
        remainder4Coefficient1.coeff (52 - (52 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 52 + x
  · rw [recurrence4LeadingSquare_coeff_high (52 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (52 - (52 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_52 :
    recurrence4Scalar1Left.coeff 52 =
      (((3560679445490136693662319550 * 10 ^ 70 +
        4647344494608828640323442988044477726519204161207628088669710350554821) * 10 ^ 70 +
        6527557643248453634950335476913092626890225239088447104248380336495307) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 53,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (52 - x)) = _
  rw [show 53 = 0 +
    53 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 20 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_52_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_53_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (53 + x) *
        remainder4Coefficient1.coeff (53 - (53 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 53 + x
  · rw [recurrence4LeadingSquare_coeff_high (53 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (53 - (53 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_53 :
    recurrence4Scalar1Left.coeff 53 =
      -(((238646809675073624706211386436 * 10 ^ 70 +
        4141306506171006693083216261805812214440741256522335866169879438367425) * 10 ^ 70 +
        3560394786854932913407908441894571920508140415362523344006947170201688) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 54,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (53 - x)) = _
  rw [show 54 = 0 +
    54 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_53_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_54_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (54 + x) *
        remainder4Coefficient1.coeff (54 - (54 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 54 + x
  · rw [recurrence4LeadingSquare_coeff_high (54 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (54 - (54 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_54 :
    recurrence4Scalar1Left.coeff 54 =
      (((14836786514148983290105204548637 * 10 ^ 70 +
        6587187293508553269601859475571523704217474189671877080096985616506811) * 10 ^ 70 +
        8058757587765952306334152399140680840848249995540124865331357280859805) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 55,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (54 - x)) = _
  rw [show 55 = 0 +
    55 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 22 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_54_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_55_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (55 + x) *
        remainder4Coefficient1.coeff (55 - (55 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 55 + x
  · rw [recurrence4LeadingSquare_coeff_high (55 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (55 - (55 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_55 :
    recurrence4Scalar1Left.coeff 55 =
      -(((860447010897594386915041264688006 * 10 ^ 70 +
        5265920558591492832269040048350859057150167833076428391937893708536744) * 10 ^ 70 +
        9545687732039591013881292421284666174229994695004407607661927952325489) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 56,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (55 - x)) = _
  rw [show 56 = 0 +
    56 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 56 = 32 +
      24 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 24 = 23 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_55_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_56_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (56 + x) *
        remainder4Coefficient1.coeff (56 - (56 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 56 + x
  · rw [recurrence4LeadingSquare_coeff_high (56 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (56 - (56 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_56 :
    recurrence4Scalar1Left.coeff 56 =
      (((46742964372635072294072957003256544 * 10 ^ 70 +
        4904727091637327378814984400813374904218998835370483493206938808708853) * 10 ^ 70 +
        9375192573660945834370959759206586832704162003901519962842455986849666) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 57,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (56 - x)) = _
  rw [show 57 = 0 +
    57 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 24 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_56_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_57_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (57 + x) *
        remainder4Coefficient1.coeff (57 - (57 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 57 + x
  · rw [recurrence4LeadingSquare_coeff_high (57 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (57 - (57 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_57 :
    recurrence4Scalar1Left.coeff 57 =
      -(((2386216665867495163519465091104100735 * 10 ^ 70 +
        1907936441170802483191698657078080190816223344543582264579029549836029) * 10 ^ 70 +
        9047086916480904166455746045302324492675210655788063413020486493014131) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 58,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (57 - x)) = _
  rw [show 58 = 0 +
    58 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_57_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_58_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (58 + x) *
        remainder4Coefficient1.coeff (58 - (58 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 58 + x
  · rw [recurrence4LeadingSquare_coeff_high (58 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (58 - (58 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_58 :
    recurrence4Scalar1Left.coeff 58 =
      (((114765201730165933141693608321536500188 * 10 ^ 70 +
        7382531825053547069957739742583549980024061209554012745228799589462386) * 10 ^ 70 +
        2696726090768896127999945140139119095395214778587672750965328414116970) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 59,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (58 - x)) = _
  rw [show 59 = 0 +
    59 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 26 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_58_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_59_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (59 + x) *
        remainder4Coefficient1.coeff (59 - (59 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 59 + x
  · rw [recurrence4LeadingSquare_coeff_high (59 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (59 - (59 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_59 :
    recurrence4Scalar1Left.coeff 59 =
      -(((5210875159667630936719224841498579927975 * 10 ^ 70 +
        6856249408647331795947989159777786803072861048405605265955119854644814) * 10 ^ 70 +
        7875165961771509647075662453475601817506846425321267945540017287272128) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 60,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (59 - x)) = _
  rw [show 60 = 0 +
    60 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 60 = 32 +
      28 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 28 = 27 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_59_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_60_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (60 + x) *
        remainder4Coefficient1.coeff (60 - (60 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 60 + x
  · rw [recurrence4LeadingSquare_coeff_high (60 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (60 - (60 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_60 :
    recurrence4Scalar1Left.coeff 60 =
      (((223738594196880232461554248417531322898954 * 10 ^ 70 +
        7016823691268610999203068389219404389291632299746922216999937936891549) * 10 ^ 70 +
        5452978925730142787868006974668739393136901899950988218424626420984124) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 61,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (60 - x)) = _
  rw [show 61 = 0 +
    61 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 61 = 32 +
      29 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 29 = 28 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_60_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_61_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (61 + x) *
        remainder4Coefficient1.coeff (61 - (61 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 61 + x
  · rw [recurrence4LeadingSquare_coeff_high (61 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (61 - (61 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_61 :
    recurrence4Scalar1Left.coeff 61 =
      -(((9096987294408812842074380093160974537091082 * 10 ^ 70 +
        3204832670381819113453642940792988055689068156606539976185468732631170) * 10 ^ 70 +
        0368662891600321197146854251398542174155105780570175058582533381925572) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 62,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (61 - x)) = _
  rw [show 62 = 0 +
    62 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 62 = 32 +
      30 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 30 = 29 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_61_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_62_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (62 + x) *
        remainder4Coefficient1.coeff (62 - (62 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 62 + x
  · rw [recurrence4LeadingSquare_coeff_high (62 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (62 - (62 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_62 :
    recurrence4Scalar1Left.coeff 62 =
      (((350641481928570222263478078266082979191703866 * 10 ^ 70 +
        9235609072650698007686601735613198215683923741117847445691302442993742) * 10 ^ 70 +
        9971172206746708703087862030096286737605837989009835841634093464442485) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 63,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (62 - x)) = _
  rw [show 63 = 0 +
    63 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_62_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_63_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (63 + x) *
        remainder4Coefficient1.coeff (63 - (63 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 63 + x
  · rw [recurrence4LeadingSquare_coeff_high (63 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (63 - (63 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_63 :
    recurrence4Scalar1Left.coeff 63 =
      -(((12823808366569304465001724623884927802456498291 * 10 ^ 70 +
        9969983796099265273748866418791053591085291967605405685769401837610523) * 10 ^ 70 +
        4168215909657886497860008241588146969861930893181790973108078775779987) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 64,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (63 - x)) = _
  rw [show 64 = 0 +
    64 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 31 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_63_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_64_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (64 + x) *
        remainder4Coefficient1.coeff (64 - (64 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 64 + x
  · rw [recurrence4LeadingSquare_coeff_high (64 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (64 - (64 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_64 :
    recurrence4Scalar1Left.coeff 64 =
      (((445284741373591801078605305672985401823601325496 * 10 ^ 70 +
        5530801315266029942761163081991696212557191768215546373468357062459479) * 10 ^ 70 +
        9843808370801173515709496157274526438564892382348949360444765766899993) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 65,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (64 - x)) = _
  rw [show 65 = 0 +
    65 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 65 = 32 +
      33 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 33 = 32 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_64_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_65_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (65 + x) *
        remainder4Coefficient1.coeff (65 - (65 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 65 + x
  · rw [recurrence4LeadingSquare_coeff_high (65 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (65 - (65 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_65 :
    recurrence4Scalar1Left.coeff 65 =
      -(((14685946089273671127277102050077392688640489173671 * 10 ^ 70 +
        3369080307753899659948392867563739013794184714393524295305836441440582) * 10 ^ 70 +
        3573338226450530566029013851835824820283823337100393178033835932774035) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 66,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (65 - x)) = _
  rw [show 66 = 0 +
    66 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 66 = 32 +
      34 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 34 = 32 +
      2 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 2 = 1 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_65_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_66_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (66 + x) *
        remainder4Coefficient1.coeff (66 - (66 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 66 + x
  · rw [recurrence4LeadingSquare_coeff_high (66 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (66 - (66 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_66 :
    recurrence4Scalar1Left.coeff 66 =
      (((460121910934922548055121423059897461076770400474722 * 10 ^ 70 +
        1258019505228362489233071073004623390128835813067357314083796418291910) * 10 ^ 70 +
        2933449273451948981283574011047813536830572833175748483766321368409517) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 67,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (66 - x)) = _
  rw [show 67 = 0 +
    67 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_66_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_67_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (67 + x) *
        remainder4Coefficient1.coeff (67 - (67 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 67 + x
  · rw [recurrence4LeadingSquare_coeff_high (67 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (67 - (67 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_67 :
    recurrence4Scalar1Left.coeff 67 =
      -(((13692500228338617985877875048806420663373835425181025 * 10 ^ 70 +
        2615731608165097880640727509892121915318074024056398614173181858510825) * 10 ^ 70 +
        1470346815514409985843539542685648913225142788783032499120439357642556) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 68,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (67 - x)) = _
  rw [show 68 = 0 +
    68 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 68 = 32 +
      36 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 36 = 32 +
      4 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 4 = 3 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_67_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_68_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (68 + x) *
        remainder4Coefficient1.coeff (68 - (68 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 68 + x
  · rw [recurrence4LeadingSquare_coeff_high (68 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (68 - (68 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_68 :
    recurrence4Scalar1Left.coeff 68 =
      (((386812428029844055545897810595385365863151180546812759 * 10 ^ 70 +
        4620160469540114108078017996693006107924004381483026570338740879107311) * 10 ^ 70 +
        5225654811531264242027628243624435737429930960160157004798537253261952) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 69,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (68 - x)) = _
  rw [show 69 = 0 +
    69 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 32 +
      5 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 5 = 4 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_68_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_69_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (69 + x) *
        remainder4Coefficient1.coeff (69 - (69 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 69 + x
  · rw [recurrence4LeadingSquare_coeff_high (69 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (69 - (69 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_69 :
    recurrence4Scalar1Left.coeff 69 =
      -(((10362891398884054381157678296779478938966774179586587648 * 10 ^ 70 +
        3120303204651012185444888839768890028628971745664567383476460472141421) * 10 ^ 70 +
        3396181779674732956463888731845972429674708206745698559577191077728288) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 70,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (69 - x)) = _
  rw [show 70 = 0 +
    70 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 70 = 32 +
      38 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 38 = 32 +
      6 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 6 = 5 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_69_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_70_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (70 + x) *
        remainder4Coefficient1.coeff (70 - (70 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 70 + x
  · rw [recurrence4LeadingSquare_coeff_high (70 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (70 - (70 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_70 :
    recurrence4Scalar1Left.coeff 70 =
      (((262834534570918265924859582973296467155649575441531300942 * 10 ^ 70 +
        0152975579874813740810233484226540240232651321417949087604842321580769) * 10 ^ 70 +
        5048059233583509320184263296298291703231545068894593228816909215869509) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 71,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (70 - x)) = _
  rw [show 71 = 0 +
    71 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 71 = 32 +
      39 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 39 = 32 +
      7 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 7 = 6 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_70_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_71_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (71 + x) *
        remainder4Coefficient1.coeff (71 - (71 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 71 + x
  · rw [recurrence4LeadingSquare_coeff_high (71 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (71 - (71 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_71 :
    recurrence4Scalar1Left.coeff 71 =
      -(((6293989670181592235016332602295101387829989261085438577955 * 10 ^ 70 +
        4600304166630872454343665481268687728452509453689892288180394475626303) * 10 ^ 70 +
        7992432390920348999397602249737382195501576748086737702988558661803898) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 72,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (71 - x)) = _
  rw [show 72 = 0 +
    72 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 72 = 32 +
      40 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 40 = 32 +
      8 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 8 = 7 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_71_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_72_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (72 + x) *
        remainder4Coefficient1.coeff (72 - (72 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 72 + x
  · rw [recurrence4LeadingSquare_coeff_high (72 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (72 - (72 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_72 :
    recurrence4Scalar1Left.coeff 72 =
      (((141692697025926772899155886331354035503894189025498995750862 * 10 ^ 70 +
        5115399134217000855242725012174807279109370154950764524786577064757357) * 10 ^ 70 +
        5261281937729863266322240661404374283432979179499407835860932828720898) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 73,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (72 - x)) = _
  rw [show 73 = 0 +
    73 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 73 = 32 +
      41 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 41 = 32 +
      9 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 9 = 8 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_72_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_73_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (73 + x) *
        remainder4Coefficient1.coeff (73 - (73 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 73 + x
  · rw [recurrence4LeadingSquare_coeff_high (73 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (73 - (73 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_73 :
    recurrence4Scalar1Left.coeff 73 =
      -(((2977984861340611018823121761970407706910997721066846574446565 * 10 ^ 70 +
        7805324934295045106160888420637470993378943910155543154887642668285641) * 10 ^ 70 +
        5781375178675759466112660908163798170999522144727434806741046822482320) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 74,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (73 - x)) = _
  rw [show 74 = 0 +
    74 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 74 = 32 +
      42 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 42 = 32 +
      10 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 10 = 9 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_73_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_74_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (74 + x) *
        remainder4Coefficient1.coeff (74 - (74 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 74 + x
  · rw [recurrence4LeadingSquare_coeff_high (74 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (74 - (74 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_74 :
    recurrence4Scalar1Left.coeff 74 =
      (((57738442344721287215089886848936175877840210588918246766682761 * 10 ^ 70 +
        0408708600045991348866855012557095907504682872654688907855401071968475) * 10 ^ 70 +
        0340328575376606051615884953787294458326655913630536335612987862360050) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 75,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (74 - x)) = _
  rw [show 75 = 0 +
    75 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 75 = 32 +
      43 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 43 = 32 +
      11 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 11 = 10 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_74_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
