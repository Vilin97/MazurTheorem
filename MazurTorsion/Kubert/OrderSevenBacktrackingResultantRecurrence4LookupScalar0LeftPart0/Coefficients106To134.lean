/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupLeadingSquare
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupA0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar0LeftPart0Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar0Left coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4A0_coeff_1
  recurrence4A0_coeff_10
  recurrence4A0_coeff_100
  recurrence4A0_coeff_101
  recurrence4A0_coeff_102
  recurrence4A0_coeff_103
  recurrence4A0_coeff_104
  recurrence4A0_coeff_105
  recurrence4A0_coeff_106
  recurrence4A0_coeff_107
  recurrence4A0_coeff_108
  recurrence4A0_coeff_109
  recurrence4A0_coeff_11
  recurrence4A0_coeff_110
  recurrence4A0_coeff_111
  recurrence4A0_coeff_112
  recurrence4A0_coeff_113
  recurrence4A0_coeff_114
  recurrence4A0_coeff_115
  recurrence4A0_coeff_116
  recurrence4A0_coeff_117
  recurrence4A0_coeff_118
  recurrence4A0_coeff_119
  recurrence4A0_coeff_12
  recurrence4A0_coeff_120
  recurrence4A0_coeff_121
  recurrence4A0_coeff_122
  recurrence4A0_coeff_123
  recurrence4A0_coeff_124
  recurrence4A0_coeff_125
  recurrence4A0_coeff_126
  recurrence4A0_coeff_127
  recurrence4A0_coeff_128
  recurrence4A0_coeff_129
  recurrence4A0_coeff_13
  recurrence4A0_coeff_130
  recurrence4A0_coeff_131
  recurrence4A0_coeff_132
  recurrence4A0_coeff_133
  recurrence4A0_coeff_134
  recurrence4A0_coeff_135
  recurrence4A0_coeff_136
  recurrence4A0_coeff_137
  recurrence4A0_coeff_138
  recurrence4A0_coeff_139
  recurrence4A0_coeff_14
  recurrence4A0_coeff_140
  recurrence4A0_coeff_141
  recurrence4A0_coeff_142
  recurrence4A0_coeff_143
  recurrence4A0_coeff_144
  recurrence4A0_coeff_145
  recurrence4A0_coeff_146
  recurrence4A0_coeff_147
  recurrence4A0_coeff_148
  recurrence4A0_coeff_149
  recurrence4A0_coeff_15
  recurrence4A0_coeff_150
  recurrence4A0_coeff_151
  recurrence4A0_coeff_152
  recurrence4A0_coeff_153
  recurrence4A0_coeff_154
  recurrence4A0_coeff_155
  recurrence4A0_coeff_156

attribute [local simp]
  recurrence4A0_coeff_157
  recurrence4A0_coeff_158
  recurrence4A0_coeff_159
  recurrence4A0_coeff_16
  recurrence4A0_coeff_160
  recurrence4A0_coeff_161
  recurrence4A0_coeff_162
  recurrence4A0_coeff_17
  recurrence4A0_coeff_18
  recurrence4A0_coeff_19
  recurrence4A0_coeff_2
  recurrence4A0_coeff_20
  recurrence4A0_coeff_21
  recurrence4A0_coeff_22
  recurrence4A0_coeff_23
  recurrence4A0_coeff_24
  recurrence4A0_coeff_25
  recurrence4A0_coeff_26
  recurrence4A0_coeff_27
  recurrence4A0_coeff_28
  recurrence4A0_coeff_29
  recurrence4A0_coeff_3
  recurrence4A0_coeff_30
  recurrence4A0_coeff_31
  recurrence4A0_coeff_32
  recurrence4A0_coeff_33
  recurrence4A0_coeff_34
  recurrence4A0_coeff_35
  recurrence4A0_coeff_36
  recurrence4A0_coeff_37
  recurrence4A0_coeff_38
  recurrence4A0_coeff_39
  recurrence4A0_coeff_4
  recurrence4A0_coeff_40
  recurrence4A0_coeff_41
  recurrence4A0_coeff_42
  recurrence4A0_coeff_43
  recurrence4A0_coeff_44
  recurrence4A0_coeff_45
  recurrence4A0_coeff_46
  recurrence4A0_coeff_47
  recurrence4A0_coeff_48
  recurrence4A0_coeff_49
  recurrence4A0_coeff_5
  recurrence4A0_coeff_50
  recurrence4A0_coeff_51
  recurrence4A0_coeff_52
  recurrence4A0_coeff_53
  recurrence4A0_coeff_54
  recurrence4A0_coeff_55
  recurrence4A0_coeff_56
  recurrence4A0_coeff_57
  recurrence4A0_coeff_58
  recurrence4A0_coeff_59
  recurrence4A0_coeff_6
  recurrence4A0_coeff_60
  recurrence4A0_coeff_61
  recurrence4A0_coeff_62
  recurrence4A0_coeff_63
  recurrence4A0_coeff_64
  recurrence4A0_coeff_65
  recurrence4A0_coeff_66
  recurrence4A0_coeff_67
  recurrence4A0_coeff_68

attribute [local simp]
  recurrence4A0_coeff_69
  recurrence4A0_coeff_7
  recurrence4A0_coeff_70
  recurrence4A0_coeff_71
  recurrence4A0_coeff_72
  recurrence4A0_coeff_73
  recurrence4A0_coeff_74
  recurrence4A0_coeff_75
  recurrence4A0_coeff_76
  recurrence4A0_coeff_77
  recurrence4A0_coeff_78
  recurrence4A0_coeff_79
  recurrence4A0_coeff_8
  recurrence4A0_coeff_80
  recurrence4A0_coeff_81
  recurrence4A0_coeff_82
  recurrence4A0_coeff_83
  recurrence4A0_coeff_84
  recurrence4A0_coeff_85
  recurrence4A0_coeff_86
  recurrence4A0_coeff_87
  recurrence4A0_coeff_88
  recurrence4A0_coeff_89
  recurrence4A0_coeff_9
  recurrence4A0_coeff_90
  recurrence4A0_coeff_91
  recurrence4A0_coeff_92
  recurrence4A0_coeff_93
  recurrence4A0_coeff_94
  recurrence4A0_coeff_95
  recurrence4A0_coeff_96
  recurrence4A0_coeff_97
  recurrence4A0_coeff_98
  recurrence4A0_coeff_99
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

private theorem recurrence4Scalar0Left_coeff_106_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (106 + x) *
        remainder4Coefficient0.coeff (106 - (106 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 106 + x
  · rw [recurrence4LeadingSquare_coeff_high (106 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (106 - (106 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_106 :
    recurrence4Scalar0Left.coeff 106 =
      ((((547752597517484859419774155918 * 10 ^ 70 +
        5664935105567559126296457101284405237653628860979709578883167742396298) * 10 ^ 70 +
        1892779265035573228593331574669255020260515037955672296374866763977821) * 10 ^ 70 +
        5100805850843484502584134515684846713623197854435309545902101580846887) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 107,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (106 - x)) = _
  rw [show 107 = 0 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
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
  rw [recurrence4Scalar0Left_coeff_106_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_107_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (107 + x) *
        remainder4Coefficient0.coeff (107 - (107 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 107 + x
  · rw [recurrence4LeadingSquare_coeff_high (107 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (107 - (107 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_107 :
    recurrence4Scalar0Left.coeff 107 =
      -((((6046423409505427397799281062817 * 10 ^ 70 +
        2806619779844032953700390431955912022278242599398626075661595475647120) * 10 ^ 70 +
        6821485943918508478208957860502606439402644405119585733422245740137000) * 10 ^ 70 +
        5989419290267414580155255763402077961642021882744245425077452521957605) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 108,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (107 - x)) = _
  rw [show 108 = 0 +
    108 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 108 = 32 +
      76 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 76 = 32 +
      44 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 44 = 32 +
      12 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 12 = 11 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_107_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_108_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (108 + x) *
        remainder4Coefficient0.coeff (108 - (108 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 108 + x
  · rw [recurrence4LeadingSquare_coeff_high (108 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (108 - (108 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_108 :
    recurrence4Scalar0Left.coeff 108 =
      ((((64888636197293623194179400160150 * 10 ^ 70 +
        0361405332940038697200285525896327440211717365892964081590851197349794) * 10 ^ 70 +
        8896116488808104924277622362146690217133282059744178114809314052918408) * 10 ^ 70 +
        1534628555378287335896398221800616475103089025752358631742338651776472) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 109,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (108 - x)) = _
  rw [show 109 = 0 +
    109 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 109 = 32 +
      77 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 77 = 32 +
      45 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 12 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_108_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_109_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (109 + x) *
        remainder4Coefficient0.coeff (109 - (109 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 109 + x
  · rw [recurrence4LeadingSquare_coeff_high (109 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (109 - (109 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_109 :
    recurrence4Scalar0Left.coeff 109 =
      -((((677491727254049457797154536070737 * 10 ^ 70 +
        5764572015648194036935071872540969394396712571019314707303415006913886) * 10 ^ 70 +
        2436573065085164886760122349121257612659779930583607308114937766410416) * 10 ^ 70 +
        4324428336983565751514925943465800453670948010295484741426325698809343) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 110,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (109 - x)) = _
  rw [show 110 = 0 +
    110 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 110 = 32 +
      78 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 78 = 32 +
      46 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 46 = 32 +
      14 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 14 = 13 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_109_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_110_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (110 + x) *
        remainder4Coefficient0.coeff (110 - (110 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 110 + x
  · rw [recurrence4LeadingSquare_coeff_high (110 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (110 - (110 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_110 :
    recurrence4Scalar0Left.coeff 110 =
      ((((6886247756142637379368605968014456 * 10 ^ 70 +
        1789872556566126441800893153699543114194484575908800510808524459472940) * 10 ^ 70 +
        4957807168470975020443890216831168333129352272060713812479620094858552) * 10 ^ 70 +
        5640126116643238332509441559599565441616967413555592554297332317447350) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 111,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (110 - x)) = _
  rw [show 111 = 0 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 32 +
      47 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 47 = 32 +
      15 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 15 = 14 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_110_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_111_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (111 + x) *
        remainder4Coefficient0.coeff (111 - (111 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 111 + x
  · rw [recurrence4LeadingSquare_coeff_high (111 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (111 - (111 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_111 :
    recurrence4Scalar0Left.coeff 111 =
      -((((68179974356060145067112651917991212 * 10 ^ 70 +
        0311326774422926020481685540816432441605069100023923153541955358815064) * 10 ^ 70 +
        8501312982621269657171862204259598982798115086854369776547542483329855) * 10 ^ 70 +
        9657353638143753248943069551431117913665657338248897490717844848414825) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 112,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (111 - x)) = _
  rw [show 112 = 0 +
    112 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 112 = 32 +
      80 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 80 = 32 +
      48 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 48 = 32 +
      16 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 16 = 15 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_111_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_112_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (112 + x) *
        remainder4Coefficient0.coeff (112 - (112 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 112 + x
  · rw [recurrence4LeadingSquare_coeff_high (112 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (112 - (112 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_112 :
    recurrence4Scalar0Left.coeff 112 =
      ((((657895998352260826275264960870876777 * 10 ^ 70 +
        8230625291278692745650817298585867298371898980984266101751344606417138) * 10 ^ 70 +
        3757091008542331227756906207958770657025090606860713861579277626463541) * 10 ^ 70 +
        5431205519766912060118789434614361755385629312732769740387559373929735) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 113,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (112 - x)) = _
  rw [show 113 = 0 +
    113 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 113 = 32 +
      81 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 16 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_112_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_113_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (113 + x) *
        remainder4Coefficient0.coeff (113 - (113 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 113 + x
  · rw [recurrence4LeadingSquare_coeff_high (113 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (113 - (113 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_113 :
    recurrence4Scalar0Left.coeff 113 =
      -((((6190080780075539133652046739755224996 * 10 ^ 70 +
        5358541766075477840171706955383280951355951044351052300646840160976884) * 10 ^ 70 +
        8702826771942192042599605726093886744664464852757950328850336753007391) * 10 ^ 70 +
        0129190594395617567875828609253605836612635713541829687919746491328128) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 114,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (113 - x)) = _
  rw [show 114 = 0 +
    114 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 17 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_113_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_114_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (114 + x) *
        remainder4Coefficient0.coeff (114 - (114 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 114 + x
  · rw [recurrence4LeadingSquare_coeff_high (114 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (114 - (114 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_114 :
    recurrence4Scalar0Left.coeff 114 =
      ((((56816031556860573638995686098177696629 * 10 ^ 70 +
        7732046264339603443734573488159283945915471394446847034797131875220481) * 10 ^ 70 +
        3072652277306571119823816383135013276637911932005839207554375883475179) * 10 ^ 70 +
        2232910304022351527434826446459704523265644233726996504523348763102887) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 115,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (114 - x)) = _
  rw [show 115 = 0 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 19 = 18 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_114_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_115_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (115 + x) *
        remainder4Coefficient0.coeff (115 - (115 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 115 + x
  · rw [recurrence4LeadingSquare_coeff_high (115 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (115 - (115 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_115 :
    recurrence4Scalar0Left.coeff 115 =
      -((((508937408278338384276460037887685912900 * 10 ^ 70 +
        2289101240902219947954758654537838279373167657048550430027544941453304) * 10 ^ 70 +
        1180642260577827267703130689196087917178320881755979790082362255090546) * 10 ^ 70 +
        7332074116281751332444594270789963178120959941283718101208040840654972) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 116,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (115 - x)) = _
  rw [show 116 = 0 +
    116 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 116 = 32 +
      84 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 84 = 32 +
      52 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 52 = 32 +
      20 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 20 = 19 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_115_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_116_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (116 + x) *
        remainder4Coefficient0.coeff (116 - (116 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 116 + x
  · rw [recurrence4LeadingSquare_coeff_high (116 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (116 - (116 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_116 :
    recurrence4Scalar0Left.coeff 116 =
      ((((4450905982870626392489645287647757598194 * 10 ^ 70 +
        9731050712205768138782620388583925381643450642971914330151052373761463) * 10 ^ 70 +
        2145402992841643279979421273030477029560521211120918751259104728044326) * 10 ^ 70 +
        2169672172637062055228374430302189391343686863569909190624100675051253) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 117,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (116 - x)) = _
  rw [show 117 = 0 +
    117 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 117 = 32 +
      85 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 20 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_116_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_117_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (117 + x) *
        remainder4Coefficient0.coeff (117 - (117 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 117 + x
  · rw [recurrence4LeadingSquare_coeff_high (117 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (117 - (117 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_117 :
    recurrence4Scalar0Left.coeff 117 =
      -((((38017575534284951748772830166757768888348 * 10 ^ 70 +
        9144781627310629193477330838720939463725959958240847227468380952697454) * 10 ^ 70 +
        1683510593837223335178288397915591616380920256964795605525263642453489) * 10 ^ 70 +
        0129461455985402829846964318311046924155907149468102213704856828450978) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 118,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (117 - x)) = _
  rw [show 118 = 0 +
    118 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_117_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_118_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (118 + x) *
        remainder4Coefficient0.coeff (118 - (118 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 118 + x
  · rw [recurrence4LeadingSquare_coeff_high (118 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (118 - (118 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_118 :
    recurrence4Scalar0Left.coeff 118 =
      ((((317266808482271799175914024478997158580677 * 10 ^ 70 +
        2387384777210730886291666841254942407731924854779587688949423869189526) * 10 ^ 70 +
        9380268438188978954386465333694367796758375586921100092236157153495953) * 10 ^ 70 +
        9550110563735188012736412795306574459182202526387299160722396774796981) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 119,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (118 - x)) = _
  rw [show 119 = 0 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 22 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_118_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_119_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (119 + x) *
        remainder4Coefficient0.coeff (119 - (119 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 119 + x
  · rw [recurrence4LeadingSquare_coeff_high (119 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (119 - (119 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_119 :
    recurrence4Scalar0Left.coeff 119 =
      -((((2587695971718547610149028969810437232374413 * 10 ^ 70 +
        1276667031358898827475136195073918291404948334052999037387083128695132) * 10 ^ 70 +
        0713601382049434376763124625311389193607855524825090372945695422577009) * 10 ^ 70 +
        1728865365225240095504081457955692764138573276942062569285378021244397) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 120,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (119 - x)) = _
  rw [show 120 = 0 +
    120 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 120 = 32 +
      88 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 88 = 32 +
      56 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 56 = 32 +
      24 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 24 = 23 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_119_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_120_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (120 + x) *
        remainder4Coefficient0.coeff (120 - (120 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 120 + x
  · rw [recurrence4LeadingSquare_coeff_high (120 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (120 - (120 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_120 :
    recurrence4Scalar0Left.coeff 120 =
      ((((20634176003573188128709480168691432135810172 * 10 ^ 70 +
        9339440106208596486740655471603985004100764205880986987074576869442805) * 10 ^ 70 +
        9100121809879202671888102712553990616884639205667864676325899240028796) * 10 ^ 70 +
        2624072178550078724398345542187371903815692736386375095442931081405293) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 121,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (120 - x)) = _
  rw [show 121 = 0 +
    121 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 121 = 32 +
      89 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 24 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_120_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_121_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (121 + x) *
        remainder4Coefficient0.coeff (121 - (121 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 121 + x
  · rw [recurrence4LeadingSquare_coeff_high (121 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (121 - (121 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_121 :
    recurrence4Scalar0Left.coeff 121 =
      -((((160907614631005604855774422086839555606086735 * 10 ^ 70 +
        8677450497652159802001075742604834243249003274888092676674475820623380) * 10 ^ 70 +
        3710536958293681500299212661077646631399937701994263859493246645033933) * 10 ^ 70 +
        9657569386412891834770078281106185488065370076173691648103527139170256) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 122,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (121 - x)) = _
  rw [show 122 = 0 +
    122 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_121_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_122_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (122 + x) *
        remainder4Coefficient0.coeff (122 - (122 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 122 + x
  · rw [recurrence4LeadingSquare_coeff_high (122 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (122 - (122 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_122 :
    recurrence4Scalar0Left.coeff 122 =
      ((((1227456185831557800247809519643692198298386828 * 10 ^ 70 +
        0610002613216335861122778850849458541286368690701675747916823928992212) * 10 ^ 70 +
        0092442322929875890520488885446781438397001943557124891368549581111261) * 10 ^ 70 +
        3121778898543855961034283744876204869250178876617016541588934812470290) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 123,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (122 - x)) = _
  rw [show 123 = 0 +
    123 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 27 = 26 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_122_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_123_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (123 + x) *
        remainder4Coefficient0.coeff (123 - (123 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 123 + x
  · rw [recurrence4LeadingSquare_coeff_high (123 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (123 - (123 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_123 :
    recurrence4Scalar0Left.coeff 123 =
      -((((9162083508453453588520119834810048118906942341 * 10 ^ 70 +
        0133641577191825066472176868286888122836348145255630957399167963481040) * 10 ^ 70 +
        2928355248304986676508189239481379528001525863875029446374177786703366) * 10 ^ 70 +
        2904562946431313418040087761381756044174946022179522107015563987933066) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 124,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (123 - x)) = _
  rw [show 124 = 0 +
    124 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_123_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_124_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (124 + x) *
        remainder4Coefficient0.coeff (124 - (124 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 124 + x
  · rw [recurrence4LeadingSquare_coeff_high (124 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (124 - (124 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_124 :
    recurrence4Scalar0Left.coeff 124 =
      ((((66935306262582220226315271335449995880148631721 * 10 ^ 70 +
        5314478041483016656305334021595608833900723478757899364317474036068589) * 10 ^ 70 +
        7875840694496226392735131982962971096385490134693764733714834307752332) * 10 ^ 70 +
        7912141627083880085643240440621704858634707492237531083479751708180924) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 125,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (124 - x)) = _
  rw [show 125 = 0 +
    125 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 29 = 28 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_124_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_125_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (125 + x) *
        remainder4Coefficient0.coeff (125 - (125 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 125 + x
  · rw [recurrence4LeadingSquare_coeff_high (125 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (125 - (125 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_125 :
    recurrence4Scalar0Left.coeff 125 =
      -((((478738487805394099580586421973706307322379454186 * 10 ^ 70 +
        3388446789262803786766795972523057005277619551251771556004447224912134) * 10 ^ 70 +
        4928681337913576612640980001434962194356212640099065837666981417335436) * 10 ^ 70 +
        9446329306397717750744978782755843726058212605183738413814602708633071) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 126,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (125 - x)) = _
  rw [show 126 = 0 +
    126 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 30 = 29 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_125_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_126_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (126 + x) *
        remainder4Coefficient0.coeff (126 - (126 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 126 + x
  · rw [recurrence4LeadingSquare_coeff_high (126 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (126 - (126 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_126 :
    recurrence4Scalar0Left.coeff 126 =
      ((((3352961553275085163811999874486749383751948421504 * 10 ^ 70 +
        3846571608485765269774604930597404080436603617794452776621945737734822) * 10 ^ 70 +
        8704665990359791185700033014137004013338990323997393998723229485295672) * 10 ^ 70 +
        1599911030879947834766904936864605464164299627798656939366536628129444) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 127,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (126 - x)) = _
  rw [show 127 = 0 +
    127 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_126_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_127_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (127 + x) *
        remainder4Coefficient0.coeff (127 - (127 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 127 + x
  · rw [recurrence4LeadingSquare_coeff_high (127 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (127 - (127 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_127 :
    recurrence4Scalar0Left.coeff 127 =
      -((((23001017636079532241562531518964940196144890182200 * 10 ^ 70 +
        8783733871660109675055410225232494166050118999972161280875849750278754) * 10 ^ 70 +
        3099407399628829295973580247946417733373370812457069162188026081165342) * 10 ^ 70 +
        1709217492261365022611556842833855782391279571888312409824952109443247) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 128,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (127 - x)) = _
  rw [show 128 = 0 +
    128 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 32 = 31 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_127_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_128_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (128 + x) *
        remainder4Coefficient0.coeff (128 - (128 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 128 + x
  · rw [recurrence4LeadingSquare_coeff_high (128 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (128 - (128 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_128 :
    recurrence4Scalar0Left.coeff 128 =
      ((((154579248976738808453411795614315459997734933758154 * 10 ^ 70 +
        9734270124933435668131131431531151585369134978978181266749363461552868) * 10 ^ 70 +
        7807883217914958392838919293263998136965624751048105590772660797599342) * 10 ^ 70 +
        0227796058205782629088780928318474618724884165713360962866600413578687) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 129,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (128 - x)) = _
  rw [show 129 = 0 +
    129 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 33 = 32 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_128_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_129_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (129 + x) *
        remainder4Coefficient0.coeff (129 - (129 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 129 + x
  · rw [recurrence4LeadingSquare_coeff_high (129 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (129 - (129 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_129 :
    recurrence4Scalar0Left.coeff 129 =
      -((((1017969963876943359528060907196329826673394879294027 * 10 ^ 70 +
        3063816542049330337663584669703453361545471762558349483609385929203870) * 10 ^ 70 +
        3228889189539486035244158987196004303185331986345673529487428915681892) * 10 ^ 70 +
        0109507071299842539742281950622318586024282470815117320916642127328556) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 130,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (129 - x)) = _
  rw [show 130 = 0 +
    130 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 34 = 32 +
      2 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 2 = 1 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_129_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_130_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (130 + x) *
        remainder4Coefficient0.coeff (130 - (130 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 130 + x
  · rw [recurrence4LeadingSquare_coeff_high (130 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (130 - (130 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_130 :
    recurrence4Scalar0Left.coeff 130 =
      ((((6570358790066920521306235968785566652714182546128988 * 10 ^ 70 +
        2620826592353684501883791772521113353362816431185752981615942720963182) * 10 ^ 70 +
        2041400359497465384464250112806851730979760093018910779337634692912663) * 10 ^ 70 +
        9295685064525466091223887715065458998919952641046250411940285964418177) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 131,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (130 - x)) = _
  rw [show 131 = 0 +
    131 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_130_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_131_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (131 + x) *
        remainder4Coefficient0.coeff (131 - (131 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 131 + x
  · rw [recurrence4LeadingSquare_coeff_high (131 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (131 - (131 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_131 :
    recurrence4Scalar0Left.coeff 131 =
      -((((41572029477964387637749998115567568866110137856146609 * 10 ^ 70 +
        7121919950252201019738479951277174234617148622507098613448365689364017) * 10 ^ 70 +
        8373705867326298700230273214704861908066900062625505876030794950399910) * 10 ^ 70 +
        7667322229945143335880129509295305263482394410913360203791727486748985) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 132,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (131 - x)) = _
  rw [show 132 = 0 +
    132 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 36 = 32 +
      4 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 4 = 3 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_131_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_132_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (132 + x) *
        remainder4Coefficient0.coeff (132 - (132 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 132 + x
  · rw [recurrence4LeadingSquare_coeff_high (132 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (132 - (132 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_132 :
    recurrence4Scalar0Left.coeff 132 =
      ((((257902866199474941776779290542398480243905130356916501 * 10 ^ 70 +
        5030867195356958064473193790399554724080462354708532142676957032209594) * 10 ^ 70 +
        8285075088938082174150946178226978324416653407690039051535542436034211) * 10 ^ 70 +
        3668525520921301738918860463283716240265787534795255291388622587277621) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 133,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (132 - x)) = _
  rw [show 133 = 0 +
    133 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 37 = 32 +
      5 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 5 = 4 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_132_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_133_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (133 + x) *
        remainder4Coefficient0.coeff (133 - (133 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 133 + x
  · rw [recurrence4LeadingSquare_coeff_high (133 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (133 - (133 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_133 :
    recurrence4Scalar0Left.coeff 133 =
      -((((1569047034907863692883355826180082587393909494977056135 * 10 ^ 70 +
        8270755062364134696426034331659940836209980676357934911103779549682314) * 10 ^ 70 +
        3723988017517356266047398108555036382570881042230570633947530116638528) * 10 ^ 70 +
        9285675977479514589467541636370705124822402607666510800928004980327670) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 134,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (133 - x)) = _
  rw [show 134 = 0 +
    134 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 38 = 32 +
      6 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 6 = 5 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_133_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_134_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (134 + x) *
        remainder4Coefficient0.coeff (134 - (134 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 134 + x
  · rw [recurrence4LeadingSquare_coeff_high (134 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (134 - (134 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_134 :
    recurrence4Scalar0Left.coeff 134 =
      ((((9363108669755041342023435103893231988594209645781284130 * 10 ^ 70 +
        7149859568160056915094335310091271850039655883521814556983377155849980) * 10 ^ 70 +
        0350096037447818069854600022441969590700525689371455164290465170777499) * 10 ^ 70 +
        1371374342365128821767944469646478524155774741429164298031458169112010) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 135,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (134 - x)) = _
  rw [show 135 = 0 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 39 = 32 +
      7 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 7 = 6 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_134_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
