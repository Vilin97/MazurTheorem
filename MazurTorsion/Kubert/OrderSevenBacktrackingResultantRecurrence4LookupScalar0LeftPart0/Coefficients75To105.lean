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

private theorem recurrence4Scalar0Left_coeff_75_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (75 + x) *
        remainder4Coefficient0.coeff (75 - (75 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 75 + x
  · rw [recurrence4LeadingSquare_coeff_high (75 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (75 - (75 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_75 :
    recurrence4Scalar0Left.coeff 75 =
      -(((105832534607992601390946781341936154732831323104222217088851448 * 10 ^ 70 +
        9934214351316092933609306547538763337424798219349898340829761179159387) * 10 ^ 70 +
        4515992905543326714096843576117808147330229577150761276376218692201020) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 76,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (75 - x)) = _
  rw [show 76 = 0 +
    76 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  rw [recurrence4Scalar0Left_coeff_75_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_76_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (76 + x) *
        remainder4Coefficient0.coeff (76 - (76 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 76 + x
  · rw [recurrence4LeadingSquare_coeff_high (76 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (76 - (76 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_76 :
    recurrence4Scalar0Left.coeff 76 =
      (((1770268366545030571237332755521915622745178936516580995156217597 * 10 ^ 70 +
        0496475983230794100357615087969853697899763826330009305032778335686059) * 10 ^ 70 +
        8815840389438472504380624126782668735815392497947761594329818137372585) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 77,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (76 - x)) = _
  rw [show 77 = 0 +
    77 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  rw [recurrence4Scalar0Left_coeff_76_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_77_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (77 + x) *
        remainder4Coefficient0.coeff (77 - (77 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 77 + x
  · rw [recurrence4LeadingSquare_coeff_high (77 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (77 - (77 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_77 :
    recurrence4Scalar0Left.coeff 77 =
      -(((24603505950326686471548493515986848469030849201240722220176265932 * 10 ^ 70 +
        0122253321720019354770543077447014219320573741169045682304568317190767) * 10 ^ 70 +
        2581916809575856029766721412591219226781399076540399262805579046005386) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 78,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (77 - x)) = _
  rw [show 78 = 0 +
    78 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  rw [recurrence4Scalar0Left_coeff_77_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_78_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (78 + x) *
        remainder4Coefficient0.coeff (78 - (78 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 78 + x
  · rw [recurrence4LeadingSquare_coeff_high (78 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (78 - (78 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_78 :
    recurrence4Scalar0Left.coeff 78 =
      (((217926076760720290722142859219290063753548009634336733109061958085 * 10 ^ 70 +
        7060552760482739511377927516663527879844067589191608495696059322932648) * 10 ^ 70 +
        5489420132449559046845681570617919460960234270074968762058659409991969) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 79,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (78 - x)) = _
  rw [show 79 = 0 +
    79 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  rw [recurrence4Scalar0Left_coeff_78_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_79_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (79 + x) *
        remainder4Coefficient0.coeff (79 - (79 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 79 + x
  · rw [recurrence4LeadingSquare_coeff_high (79 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (79 - (79 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_79 :
    recurrence4Scalar0Left.coeff 79 =
      (((1673048639643041946495720815330164736389579028738234457532966138561 * 10 ^ 70 +
        4139134060903693740819582752074656954601015102039424799611516548854347) * 10 ^ 70 +
        0456911714231995683263632626612181058624148438699425644727844322003118) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 80,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (79 - x)) = _
  rw [show 80 = 0 +
    80 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  rw [recurrence4Scalar0Left_coeff_79_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_80_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (80 + x) *
        remainder4Coefficient0.coeff (80 - (80 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 80 + x
  · rw [recurrence4LeadingSquare_coeff_high (80 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (80 - (80 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_80 :
    recurrence4Scalar0Left.coeff 80 =
      -(((150354273604292061758884674484842375753657384723692167592568943023249 * 10 ^ 70 +
        6153159458717098656821212263670528671372714752218782263734229721932027) * 10 ^ 70 +
        3327212050189921311361794453915865938617218860491415517010013547784868) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 81,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (80 - x)) = _
  rw [show 81 = 0 +
    81 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  rw [recurrence4Scalar0Left_coeff_80_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_81_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (81 + x) *
        remainder4Coefficient0.coeff (81 - (81 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 81 + x
  · rw [recurrence4LeadingSquare_coeff_high (81 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (81 - (81 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_81 :
    recurrence4Scalar0Left.coeff 81 =
      (((4981786765728666368063660286162624166841278066940512484046434351253009 * 10 ^ 70 +
        1762129820505435569771546041626096146468711873650944412719817691803241) * 10 ^ 70 +
        2957628292413822506142328195766960965260498601481653241446174414260771) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 82,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (81 - x)) = _
  rw [show 82 = 0 +
    82 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  rw [recurrence4Scalar0Left_coeff_81_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_82_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (82 + x) *
        remainder4Coefficient0.coeff (82 - (82 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 82 + x
  · rw [recurrence4LeadingSquare_coeff_high (82 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (82 - (82 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_82 :
    recurrence4Scalar0Left.coeff 82 =
      -((((12 * 10 ^ 70 +
        7301837273871653453109977975546464419408692385790457471506556333852224) * 10 ^ 70 +
        3034948897822938594259810729028485480755012872233451767577542403496974) * 10 ^ 70 +
        5994246679932087578188387108413309425138933025214661730641388325020322) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 83,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (82 - x)) = _
  rw [show 83 = 0 +
    83 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  rw [recurrence4Scalar0Left_coeff_82_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_83_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (83 + x) *
        remainder4Coefficient0.coeff (83 - (83 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 83 + x
  · rw [recurrence4LeadingSquare_coeff_high (83 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (83 - (83 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_83 :
    recurrence4Scalar0Left.coeff 83 =
      ((((281 * 10 ^ 70 +
        1742355349828597490060188186106307788062875232531916439096158671538778) * 10 ^ 70 +
        1851440391759689462039974350351558779370356263813657871702853468035446) * 10 ^ 70 +
        9967329524969851474161804409736576708991951749878001356347818694465400) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 84,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (83 - x)) = _
  rw [show 84 = 0 +
    84 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  rw [recurrence4Scalar0Left_coeff_83_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_84_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (84 + x) *
        remainder4Coefficient0.coeff (84 - (84 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 84 + x
  · rw [recurrence4LeadingSquare_coeff_high (84 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (84 - (84 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_84 :
    recurrence4Scalar0Left.coeff 84 =
      -((((5571 * 10 ^ 70 +
        6973589885254018468354839693466303883108942971566363612041680028476878) * 10 ^ 70 +
        9319328186049321918073744999837372371027053482978597187508682344531585) * 10 ^ 70 +
        9577289611199652251477055292993631188387496235535973825782408566155892) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 85,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (84 - x)) = _
  rw [show 85 = 0 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  rw [recurrence4Scalar0Left_coeff_84_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_85_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (85 + x) *
        remainder4Coefficient0.coeff (85 - (85 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 85 + x
  · rw [recurrence4LeadingSquare_coeff_high (85 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (85 - (85 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_85 :
    recurrence4Scalar0Left.coeff 85 =
      ((((100317 * 10 ^ 70 +
        3152013465218831836859138496288695721617237283479965790396757069383939) * 10 ^ 70 +
        8221977815766014617374053136334199863891405400821780664031781215665719) * 10 ^ 70 +
        3435523252940950997196195705774546690076512318660328109647731992782783) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 86,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (85 - x)) = _
  rw [show 86 = 0 +
    86 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  rw [recurrence4Scalar0Left_coeff_85_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_86_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (86 + x) *
        remainder4Coefficient0.coeff (86 - (86 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 86 + x
  · rw [recurrence4LeadingSquare_coeff_high (86 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (86 - (86 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_86 :
    recurrence4Scalar0Left.coeff 86 =
      -((((1639250 * 10 ^ 70 +
        1638350126170341529400106319763866406388677181850564839803270068677311) * 10 ^ 70 +
        3987037231085030036003351022021931418229307582025684864586408976312183) * 10 ^ 70 +
        7499187374975944850275754056063439010942525894124709658665692626778906) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 87,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (86 - x)) = _
  rw [show 87 = 0 +
    87 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  rw [recurrence4Scalar0Left_coeff_86_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_87_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (87 + x) *
        remainder4Coefficient0.coeff (87 - (87 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 87 + x
  · rw [recurrence4LeadingSquare_coeff_high (87 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (87 - (87 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_87 :
    recurrence4Scalar0Left.coeff 87 =
      ((((23919922 * 10 ^ 70 +
        1226624173898458764923325098378231568741821121049394705653708171688484) * 10 ^ 70 +
        7920282606404260801297533039906673418230162889374292708593296744113445) * 10 ^ 70 +
        5400135522514710789634612829207816123902688511004907483750781504432370) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 88,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (87 - x)) = _
  rw [show 88 = 0 +
    88 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  rw [recurrence4Scalar0Left_coeff_87_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_88_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (88 + x) *
        remainder4Coefficient0.coeff (88 - (88 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 88 + x
  · rw [recurrence4LeadingSquare_coeff_high (88 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (88 - (88 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_88 :
    recurrence4Scalar0Left.coeff 88 =
      -((((297325431 * 10 ^ 70 +
        3112194823407423820224136397595532040405700977289944640850403370867936) * 10 ^ 70 +
        3784577238991989068636925554490985366498050463472770150807910790631668) * 10 ^ 70 +
        0921768348613827437736365125401431371895342452280230944559253603424459) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 89,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (88 - x)) = _
  rw [show 89 = 0 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  rw [recurrence4Scalar0Left_coeff_88_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_89_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (89 + x) *
        remainder4Coefficient0.coeff (89 - (89 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 89 + x
  · rw [recurrence4LeadingSquare_coeff_high (89 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (89 - (89 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_89 :
    recurrence4Scalar0Left.coeff 89 =
      ((((2682380163 * 10 ^ 70 +
        6172666377700809967195636266173019641638348181703839262400826698472668) * 10 ^ 70 +
        4734863992658268868610745525692773497518467279450729256026565658898314) * 10 ^ 70 +
        7337910829559052052277290742847117702954285276331837678466499568964234) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 90,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (89 - x)) = _
  rw [show 90 = 0 +
    90 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  rw [recurrence4Scalar0Left_coeff_89_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_90_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (90 + x) *
        remainder4Coefficient0.coeff (90 - (90 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 90 + x
  · rw [recurrence4LeadingSquare_coeff_high (90 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (90 - (90 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_90 :
    recurrence4Scalar0Left.coeff 90 =
      -((((1167265320 * 10 ^ 70 +
        1318691109367909353441514947164116294366398751299543817199147634664391) * 10 ^ 70 +
        1478593581820974122557484500137872072600269452514704688813137558967017) * 10 ^ 70 +
        6908381415303840350261746171215610593833181357287781005324846709281582) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 91,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (90 - x)) = _
  rw [show 91 = 0 +
    91 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  rw [recurrence4Scalar0Left_coeff_90_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_91_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (91 + x) *
        remainder4Coefficient0.coeff (91 - (91 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 91 + x
  · rw [recurrence4LeadingSquare_coeff_high (91 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (91 - (91 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_91 :
    recurrence4Scalar0Left.coeff 91 =
      -((((720891350617 * 10 ^ 70 +
        8412404548108106748800997182410828552789314827821974384658605090018684) * 10 ^ 70 +
        2893587909559923665792549721733907570378843408689753966698192394093823) * 10 ^ 70 +
        5269729633881917609597894366251774188613991504706904139605961190217580) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 92,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (91 - x)) = _
  rw [show 92 = 0 +
    92 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  rw [recurrence4Scalar0Left_coeff_91_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_92_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (92 + x) *
        remainder4Coefficient0.coeff (92 - (92 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 92 + x
  · rw [recurrence4LeadingSquare_coeff_high (92 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (92 - (92 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_92 :
    recurrence4Scalar0Left.coeff 92 =
      ((((23305656252322 * 10 ^ 70 +
        3399262422030462410334262475490194061518169636224916280866558497715434) * 10 ^ 70 +
        3324917358927224806416589158759888486248942952725428970567539923233790) * 10 ^ 70 +
        9273624398854588217805561768656624430271539086256833711168192033710590) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 93,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (92 - x)) = _
  rw [show 93 = 0 +
    93 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  rw [recurrence4Scalar0Left_coeff_92_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_93_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (93 + x) *
        remainder4Coefficient0.coeff (93 - (93 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 93 + x
  · rw [recurrence4LeadingSquare_coeff_high (93 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (93 - (93 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_93 :
    recurrence4Scalar0Left.coeff 93 =
      -((((541500941232666 * 10 ^ 70 +
        8811084335905720490929652746104786873329286524791508690579347998061183) * 10 ^ 70 +
        2489666089838820706575792570828499676362074220139678678586302739725899) * 10 ^ 70 +
        5128470707859306291869926911683582876604377172646479603467973297688547) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 94,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (93 - x)) = _
  rw [show 94 = 0 +
    94 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  rw [recurrence4Scalar0Left_coeff_93_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_94_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (94 + x) *
        remainder4Coefficient0.coeff (94 - (94 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 94 + x
  · rw [recurrence4LeadingSquare_coeff_high (94 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (94 - (94 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_94 :
    recurrence4Scalar0Left.coeff 94 =
      ((((10801120164071971 * 10 ^ 70 +
        7527271279984338084602087679231794249038845163738001403248742306134420) * 10 ^ 70 +
        0535076974613238680494849541185411377750116296362633904573371203090385) * 10 ^ 70 +
        5797619579458386619985850277819319855699187889277135836456316090657606) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 95,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (94 - x)) = _
  rw [show 95 = 0 +
    95 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  rw [recurrence4Scalar0Left_coeff_94_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_95_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (95 + x) *
        remainder4Coefficient0.coeff (95 - (95 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 95 + x
  · rw [recurrence4LeadingSquare_coeff_high (95 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (95 - (95 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_95 :
    recurrence4Scalar0Left.coeff 95 =
      -((((195520904181684886 * 10 ^ 70 +
        9605159408041373721645797937635057871942479247100099667232495278655327) * 10 ^ 70 +
        5598449143641440021625457997535882255424283084119351019721329207556035) * 10 ^ 70 +
        2890543901431255903592566654736325086236095666230947506319146725531089) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 96,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (95 - x)) = _
  rw [show 96 = 0 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  rw [recurrence4Scalar0Left_coeff_95_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_96_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (96 + x) *
        remainder4Coefficient0.coeff (96 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 96 + x
  · rw [recurrence4LeadingSquare_coeff_high (96 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (96 - (96 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_96 :
    recurrence4Scalar0Left.coeff 96 =
      ((((3293327121765458463 * 10 ^ 70 +
        5189739665568590863550207078344040637263042089630665001655560507901249) * 10 ^ 70 +
        0303366534141634762367369689655977913672856181008490865621954885278230) * 10 ^ 70 +
        5297683410859280861764113987182782743430334258861520878435433635595481) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 97,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (96 - x)) = _
  rw [show 97 = 0 +
    97 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  rw [recurrence4Scalar0Left_coeff_96_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_97_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (97 + x) *
        remainder4Coefficient0.coeff (97 - (97 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 97 + x
  · rw [recurrence4LeadingSquare_coeff_high (97 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (97 - (97 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_97 :
    recurrence4Scalar0Left.coeff 97 =
      -((((52323885106779167934 * 10 ^ 70 +
        9781604901718306325025182175536158890979842883171227022028163463055693) * 10 ^ 70 +
        2012764391058947798096023124799802363867622933843783863159292921816853) * 10 ^ 70 +
        9240933170007009380043028042657682041249644750108986791798799939804889) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 98,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (97 - x)) = _
  rw [show 98 = 0 +
    98 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  rw [recurrence4Scalar0Left_coeff_97_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_98_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (98 + x) *
        remainder4Coefficient0.coeff (98 - (98 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 98 + x
  · rw [recurrence4LeadingSquare_coeff_high (98 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (98 - (98 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_98 :
    recurrence4Scalar0Left.coeff 98 =
      ((((790689453196746369879 * 10 ^ 70 +
        0515009917705799283807268613991265460978478008817943920370735063360823) * 10 ^ 70 +
        6468324798674430030720098905547828520945719948495619897453547576280700) * 10 ^ 70 +
        0223287471507567235803216014513284562131007321622643601945354269444807) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 99,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (98 - x)) = _
  rw [show 99 = 0 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  rw [recurrence4Scalar0Left_coeff_98_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_99_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (99 + x) *
        remainder4Coefficient0.coeff (99 - (99 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 99 + x
  · rw [recurrence4LeadingSquare_coeff_high (99 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (99 - (99 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_99 :
    recurrence4Scalar0Left.coeff 99 =
      -((((11427751295482303261566 * 10 ^ 70 +
        4935258101913146100876446959824364460324419561440548523231672932405872) * 10 ^ 70 +
        0580790734073699170275666512780694116529525788936551991691949836462921) * 10 ^ 70 +
        5085469181161670752888138655161892820756524865829391529811129297836639) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 100,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (99 - x)) = _
  rw [show 100 = 0 +
    100 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  rw [recurrence4Scalar0Left_coeff_99_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_100_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (100 + x) *
        remainder4Coefficient0.coeff (100 - (100 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 100 + x
  · rw [recurrence4LeadingSquare_coeff_high (100 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (100 - (100 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_100 :
    recurrence4Scalar0Left.coeff 100 =
      ((((158587895501008482492398 * 10 ^ 70 +
        8316510687979620163528872140030644433144578870786561989858367549478383) * 10 ^ 70 +
        8321389390428394213226864959473284353680431123319086331946295697567432) * 10 ^ 70 +
        0032362862975085344913798457297027223530957090107445862832816352992287) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 101,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (100 - x)) = _
  rw [show 101 = 0 +
    101 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  rw [recurrence4Scalar0Left_coeff_100_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_101_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (101 + x) *
        remainder4Coefficient0.coeff (101 - (101 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 101 + x
  · rw [recurrence4LeadingSquare_coeff_high (101 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (101 - (101 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_101 :
    recurrence4Scalar0Left.coeff 101 =
      -((((2119343666560896093707196 * 10 ^ 70 +
        7447801553911981893218984526307386025272430389502154423083122800227386) * 10 ^ 70 +
        8901551945234926700278184207775190227637309938693997316170602436733582) * 10 ^ 70 +
        8400070654306381237037956269298661710431326102168652196995133444009560) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 102,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (101 - x)) = _
  rw [show 102 = 0 +
    102 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  rw [recurrence4Scalar0Left_coeff_101_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_102_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (102 + x) *
        remainder4Coefficient0.coeff (102 - (102 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 102 + x
  · rw [recurrence4LeadingSquare_coeff_high (102 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (102 - (102 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_102 :
    recurrence4Scalar0Left.coeff 102 =
      ((((27335948379356391712975000 * 10 ^ 70 +
        1180631519234737820470549716144117066327932819145924367133595622674456) * 10 ^ 70 +
        0598564235603791923405209220943553276340069652593768332933092040972908) * 10 ^ 70 +
        1596521183931632012919090908162922909239229401342852103032882798983645) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 103,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (102 - x)) = _
  rw [show 103 = 0 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  rw [recurrence4Scalar0Left_coeff_102_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_103_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (103 + x) *
        remainder4Coefficient0.coeff (103 - (103 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 103 + x
  · rw [recurrence4LeadingSquare_coeff_high (103 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (103 - (103 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_103 :
    recurrence4Scalar0Left.coeff 103 =
      -((((340917400671477545617271403 * 10 ^ 70 +
        8593353681087517582061189721311779290944425498767416590613086997515026) * 10 ^ 70 +
        7714246994602292194699376317526354530821032494894843646646995891073427) * 10 ^ 70 +
        8075334712044828536457677029234581816644916420245856260887320306739351) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 104,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (103 - x)) = _
  rw [show 104 = 0 +
    104 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 104 = 32 +
      72 by norm_num, Finset.sum_range_add]
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
  rw [recurrence4Scalar0Left_coeff_103_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_104_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (104 + x) *
        remainder4Coefficient0.coeff (104 - (104 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 104 + x
  · rw [recurrence4LeadingSquare_coeff_high (104 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (104 - (104 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_104 :
    recurrence4Scalar0Left.coeff 104 =
      ((((4117045549774448030510618911 * 10 ^ 70 +
        7170354777767147546061934995531610200566770009507179873086075178582129) * 10 ^ 70 +
        0083906326977056943312703687405074499677945935225953354465085203842150) * 10 ^ 70 +
        9625520314293110338377612435975834409654905044184119401670321809478760) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 105,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (104 - x)) = _
  rw [show 105 = 0 +
    105 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 105 = 32 +
      73 by norm_num, Finset.sum_range_add]
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
  rw [recurrence4Scalar0Left_coeff_104_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_105_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (105 + x) *
        remainder4Coefficient0.coeff (105 - (105 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 105 + x
  · rw [recurrence4LeadingSquare_coeff_high (105 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (105 - (105 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_105 :
    recurrence4Scalar0Left.coeff 105 =
      -((((48203509783147252418676414157 * 10 ^ 70 +
        0534892902855907650544977936180782703219759776944987939099428271225918) * 10 ^ 70 +
        3917664785390734959154554641258268767992735943367014406484759103987759) * 10 ^ 70 +
        1173268609024903780069879229984067329253859957412698469092309862760105) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 106,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (105 - x)) = _
  rw [show 106 = 0 +
    106 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 106 = 32 +
      74 by norm_num, Finset.sum_range_add]
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
  rw [recurrence4Scalar0Left_coeff_105_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
