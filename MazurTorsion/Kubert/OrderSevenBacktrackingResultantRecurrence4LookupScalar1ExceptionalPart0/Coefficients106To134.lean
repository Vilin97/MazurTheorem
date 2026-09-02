/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupExceptionalProduct
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupC1
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar1ExceptionalPart0Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar1Exceptional coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4C1_coeff_1
  recurrence4C1_coeff_10
  recurrence4C1_coeff_100
  recurrence4C1_coeff_101
  recurrence4C1_coeff_102
  recurrence4C1_coeff_103
  recurrence4C1_coeff_104
  recurrence4C1_coeff_105
  recurrence4C1_coeff_106
  recurrence4C1_coeff_107
  recurrence4C1_coeff_108
  recurrence4C1_coeff_109
  recurrence4C1_coeff_11
  recurrence4C1_coeff_110
  recurrence4C1_coeff_111
  recurrence4C1_coeff_112
  recurrence4C1_coeff_113
  recurrence4C1_coeff_114
  recurrence4C1_coeff_115
  recurrence4C1_coeff_116
  recurrence4C1_coeff_117
  recurrence4C1_coeff_118
  recurrence4C1_coeff_119
  recurrence4C1_coeff_12
  recurrence4C1_coeff_120
  recurrence4C1_coeff_121
  recurrence4C1_coeff_122
  recurrence4C1_coeff_123
  recurrence4C1_coeff_124
  recurrence4C1_coeff_125
  recurrence4C1_coeff_126
  recurrence4C1_coeff_127
  recurrence4C1_coeff_128
  recurrence4C1_coeff_129
  recurrence4C1_coeff_13
  recurrence4C1_coeff_130
  recurrence4C1_coeff_131
  recurrence4C1_coeff_132
  recurrence4C1_coeff_133
  recurrence4C1_coeff_134
  recurrence4C1_coeff_135
  recurrence4C1_coeff_136
  recurrence4C1_coeff_137
  recurrence4C1_coeff_138
  recurrence4C1_coeff_139
  recurrence4C1_coeff_14
  recurrence4C1_coeff_140
  recurrence4C1_coeff_141
  recurrence4C1_coeff_142
  recurrence4C1_coeff_143
  recurrence4C1_coeff_144
  recurrence4C1_coeff_145
  recurrence4C1_coeff_146
  recurrence4C1_coeff_147
  recurrence4C1_coeff_148
  recurrence4C1_coeff_149
  recurrence4C1_coeff_15
  recurrence4C1_coeff_16
  recurrence4C1_coeff_17
  recurrence4C1_coeff_18
  recurrence4C1_coeff_19
  recurrence4C1_coeff_2
  recurrence4C1_coeff_20
  recurrence4C1_coeff_21

attribute [local simp]
  recurrence4C1_coeff_22
  recurrence4C1_coeff_23
  recurrence4C1_coeff_24
  recurrence4C1_coeff_25
  recurrence4C1_coeff_26
  recurrence4C1_coeff_27
  recurrence4C1_coeff_28
  recurrence4C1_coeff_29
  recurrence4C1_coeff_3
  recurrence4C1_coeff_30
  recurrence4C1_coeff_31
  recurrence4C1_coeff_32
  recurrence4C1_coeff_33
  recurrence4C1_coeff_34
  recurrence4C1_coeff_35
  recurrence4C1_coeff_36
  recurrence4C1_coeff_37
  recurrence4C1_coeff_38
  recurrence4C1_coeff_39
  recurrence4C1_coeff_4
  recurrence4C1_coeff_40
  recurrence4C1_coeff_41
  recurrence4C1_coeff_42
  recurrence4C1_coeff_43
  recurrence4C1_coeff_44
  recurrence4C1_coeff_45
  recurrence4C1_coeff_46
  recurrence4C1_coeff_47
  recurrence4C1_coeff_48
  recurrence4C1_coeff_49
  recurrence4C1_coeff_5
  recurrence4C1_coeff_50
  recurrence4C1_coeff_51
  recurrence4C1_coeff_52
  recurrence4C1_coeff_53
  recurrence4C1_coeff_54
  recurrence4C1_coeff_55
  recurrence4C1_coeff_56
  recurrence4C1_coeff_57
  recurrence4C1_coeff_58
  recurrence4C1_coeff_59
  recurrence4C1_coeff_6
  recurrence4C1_coeff_60
  recurrence4C1_coeff_61
  recurrence4C1_coeff_62
  recurrence4C1_coeff_63
  recurrence4C1_coeff_64
  recurrence4C1_coeff_65
  recurrence4C1_coeff_66
  recurrence4C1_coeff_67
  recurrence4C1_coeff_68
  recurrence4C1_coeff_69
  recurrence4C1_coeff_7
  recurrence4C1_coeff_70
  recurrence4C1_coeff_71
  recurrence4C1_coeff_72
  recurrence4C1_coeff_73
  recurrence4C1_coeff_74
  recurrence4C1_coeff_75
  recurrence4C1_coeff_76
  recurrence4C1_coeff_77
  recurrence4C1_coeff_78
  recurrence4C1_coeff_79
  recurrence4C1_coeff_8

attribute [local simp]
  recurrence4C1_coeff_80
  recurrence4C1_coeff_81
  recurrence4C1_coeff_82
  recurrence4C1_coeff_83
  recurrence4C1_coeff_84
  recurrence4C1_coeff_85
  recurrence4C1_coeff_86
  recurrence4C1_coeff_87
  recurrence4C1_coeff_88
  recurrence4C1_coeff_89
  recurrence4C1_coeff_9
  recurrence4C1_coeff_90
  recurrence4C1_coeff_91
  recurrence4C1_coeff_92
  recurrence4C1_coeff_93
  recurrence4C1_coeff_94
  recurrence4C1_coeff_95
  recurrence4C1_coeff_96
  recurrence4C1_coeff_97
  recurrence4C1_coeff_98
  recurrence4C1_coeff_99
  recurrence4ExceptionalProduct_coeff_0
  recurrence4ExceptionalProduct_coeff_1
  recurrence4ExceptionalProduct_coeff_10
  recurrence4ExceptionalProduct_coeff_100
  recurrence4ExceptionalProduct_coeff_101
  recurrence4ExceptionalProduct_coeff_102
  recurrence4ExceptionalProduct_coeff_103
  recurrence4ExceptionalProduct_coeff_104
  recurrence4ExceptionalProduct_coeff_105
  recurrence4ExceptionalProduct_coeff_106
  recurrence4ExceptionalProduct_coeff_107
  recurrence4ExceptionalProduct_coeff_108
  recurrence4ExceptionalProduct_coeff_109
  recurrence4ExceptionalProduct_coeff_11
  recurrence4ExceptionalProduct_coeff_110
  recurrence4ExceptionalProduct_coeff_111
  recurrence4ExceptionalProduct_coeff_112
  recurrence4ExceptionalProduct_coeff_113
  recurrence4ExceptionalProduct_coeff_114
  recurrence4ExceptionalProduct_coeff_115
  recurrence4ExceptionalProduct_coeff_116
  recurrence4ExceptionalProduct_coeff_117
  recurrence4ExceptionalProduct_coeff_118
  recurrence4ExceptionalProduct_coeff_119
  recurrence4ExceptionalProduct_coeff_12
  recurrence4ExceptionalProduct_coeff_120
  recurrence4ExceptionalProduct_coeff_121
  recurrence4ExceptionalProduct_coeff_122
  recurrence4ExceptionalProduct_coeff_123
  recurrence4ExceptionalProduct_coeff_124
  recurrence4ExceptionalProduct_coeff_125
  recurrence4ExceptionalProduct_coeff_126
  recurrence4ExceptionalProduct_coeff_127
  recurrence4ExceptionalProduct_coeff_128
  recurrence4ExceptionalProduct_coeff_129
  recurrence4ExceptionalProduct_coeff_13
  recurrence4ExceptionalProduct_coeff_130
  recurrence4ExceptionalProduct_coeff_131
  recurrence4ExceptionalProduct_coeff_132
  recurrence4ExceptionalProduct_coeff_133
  recurrence4ExceptionalProduct_coeff_134
  recurrence4ExceptionalProduct_coeff_135
  recurrence4ExceptionalProduct_coeff_136

attribute [local simp]
  recurrence4ExceptionalProduct_coeff_137
  recurrence4ExceptionalProduct_coeff_138
  recurrence4ExceptionalProduct_coeff_139
  recurrence4ExceptionalProduct_coeff_14
  recurrence4ExceptionalProduct_coeff_140
  recurrence4ExceptionalProduct_coeff_141
  recurrence4ExceptionalProduct_coeff_142
  recurrence4ExceptionalProduct_coeff_143
  recurrence4ExceptionalProduct_coeff_144
  recurrence4ExceptionalProduct_coeff_145
  recurrence4ExceptionalProduct_coeff_146
  recurrence4ExceptionalProduct_coeff_147
  recurrence4ExceptionalProduct_coeff_148
  recurrence4ExceptionalProduct_coeff_149
  recurrence4ExceptionalProduct_coeff_15
  recurrence4ExceptionalProduct_coeff_150
  recurrence4ExceptionalProduct_coeff_151
  recurrence4ExceptionalProduct_coeff_152
  recurrence4ExceptionalProduct_coeff_153
  recurrence4ExceptionalProduct_coeff_154
  recurrence4ExceptionalProduct_coeff_155
  recurrence4ExceptionalProduct_coeff_156
  recurrence4ExceptionalProduct_coeff_157
  recurrence4ExceptionalProduct_coeff_158
  recurrence4ExceptionalProduct_coeff_159
  recurrence4ExceptionalProduct_coeff_16
  recurrence4ExceptionalProduct_coeff_17
  recurrence4ExceptionalProduct_coeff_18
  recurrence4ExceptionalProduct_coeff_19
  recurrence4ExceptionalProduct_coeff_2
  recurrence4ExceptionalProduct_coeff_20
  recurrence4ExceptionalProduct_coeff_21
  recurrence4ExceptionalProduct_coeff_22
  recurrence4ExceptionalProduct_coeff_23
  recurrence4ExceptionalProduct_coeff_24
  recurrence4ExceptionalProduct_coeff_25
  recurrence4ExceptionalProduct_coeff_26
  recurrence4ExceptionalProduct_coeff_27
  recurrence4ExceptionalProduct_coeff_28
  recurrence4ExceptionalProduct_coeff_29
  recurrence4ExceptionalProduct_coeff_3
  recurrence4ExceptionalProduct_coeff_30
  recurrence4ExceptionalProduct_coeff_31
  recurrence4ExceptionalProduct_coeff_32
  recurrence4ExceptionalProduct_coeff_33
  recurrence4ExceptionalProduct_coeff_34
  recurrence4ExceptionalProduct_coeff_35
  recurrence4ExceptionalProduct_coeff_36
  recurrence4ExceptionalProduct_coeff_37
  recurrence4ExceptionalProduct_coeff_38
  recurrence4ExceptionalProduct_coeff_39
  recurrence4ExceptionalProduct_coeff_4
  recurrence4ExceptionalProduct_coeff_40
  recurrence4ExceptionalProduct_coeff_41
  recurrence4ExceptionalProduct_coeff_42
  recurrence4ExceptionalProduct_coeff_43
  recurrence4ExceptionalProduct_coeff_44
  recurrence4ExceptionalProduct_coeff_45
  recurrence4ExceptionalProduct_coeff_46
  recurrence4ExceptionalProduct_coeff_47
  recurrence4ExceptionalProduct_coeff_48
  recurrence4ExceptionalProduct_coeff_49
  recurrence4ExceptionalProduct_coeff_5
  recurrence4ExceptionalProduct_coeff_50

attribute [local simp]
  recurrence4ExceptionalProduct_coeff_51
  recurrence4ExceptionalProduct_coeff_52
  recurrence4ExceptionalProduct_coeff_53
  recurrence4ExceptionalProduct_coeff_54
  recurrence4ExceptionalProduct_coeff_55
  recurrence4ExceptionalProduct_coeff_56
  recurrence4ExceptionalProduct_coeff_57
  recurrence4ExceptionalProduct_coeff_58
  recurrence4ExceptionalProduct_coeff_59
  recurrence4ExceptionalProduct_coeff_6
  recurrence4ExceptionalProduct_coeff_60
  recurrence4ExceptionalProduct_coeff_61
  recurrence4ExceptionalProduct_coeff_62
  recurrence4ExceptionalProduct_coeff_63
  recurrence4ExceptionalProduct_coeff_64
  recurrence4ExceptionalProduct_coeff_65
  recurrence4ExceptionalProduct_coeff_66
  recurrence4ExceptionalProduct_coeff_67
  recurrence4ExceptionalProduct_coeff_68
  recurrence4ExceptionalProduct_coeff_69
  recurrence4ExceptionalProduct_coeff_7
  recurrence4ExceptionalProduct_coeff_70
  recurrence4ExceptionalProduct_coeff_71
  recurrence4ExceptionalProduct_coeff_72
  recurrence4ExceptionalProduct_coeff_73
  recurrence4ExceptionalProduct_coeff_74
  recurrence4ExceptionalProduct_coeff_75
  recurrence4ExceptionalProduct_coeff_76
  recurrence4ExceptionalProduct_coeff_77
  recurrence4ExceptionalProduct_coeff_78
  recurrence4ExceptionalProduct_coeff_79
  recurrence4ExceptionalProduct_coeff_8
  recurrence4ExceptionalProduct_coeff_80
  recurrence4ExceptionalProduct_coeff_81
  recurrence4ExceptionalProduct_coeff_82
  recurrence4ExceptionalProduct_coeff_83
  recurrence4ExceptionalProduct_coeff_84
  recurrence4ExceptionalProduct_coeff_85
  recurrence4ExceptionalProduct_coeff_86
  recurrence4ExceptionalProduct_coeff_87
  recurrence4ExceptionalProduct_coeff_88
  recurrence4ExceptionalProduct_coeff_89
  recurrence4ExceptionalProduct_coeff_9
  recurrence4ExceptionalProduct_coeff_90
  recurrence4ExceptionalProduct_coeff_91
  recurrence4ExceptionalProduct_coeff_92
  recurrence4ExceptionalProduct_coeff_93
  recurrence4ExceptionalProduct_coeff_94
  recurrence4ExceptionalProduct_coeff_95
  recurrence4ExceptionalProduct_coeff_96
  recurrence4ExceptionalProduct_coeff_97
  recurrence4ExceptionalProduct_coeff_98
  recurrence4ExceptionalProduct_coeff_99

private theorem recurrence4Scalar1Exceptional_coeff_106_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (106 + x) *
        remainder6Coefficient1.coeff (106 - (106 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 106 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (106 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (106 - (106 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_106 :
    recurrence4Scalar1Exceptional.coeff 106 =
      ((((674221405865227575865926461 * 10 ^ 70 +
        8336456766220096500052111440374115826388957378240769675857620205130421) * 10 ^ 70 +
        8809302301639416709515078964525646515263566341111613748671297383775482) * 10 ^ 70 +
        3968767112351334201685407190862961863541488048074837895941525674158321) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 107,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (106 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_106_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_107_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (107 + x) *
        remainder6Coefficient1.coeff (107 - (107 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 107 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (107 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (107 - (107 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_107 :
    recurrence4Scalar1Exceptional.coeff 107 =
      -((((5300621664329724732787778996 * 10 ^ 70 +
        0650227969946789838464829257142893427408450119955226933736535867113089) * 10 ^ 70 +
        0309163270405282397421458226315996390219106435923242300409626102686558) * 10 ^ 70 +
        2066410711582528266913474818908864581483102266112963987676114874055336) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 108,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (107 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_107_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_108_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (108 + x) *
        remainder6Coefficient1.coeff (108 - (108 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 108 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (108 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (108 - (108 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_108 :
    recurrence4Scalar1Exceptional.coeff 108 =
      ((((39532626765080854489544424944 * 10 ^ 70 +
        0792211964096500941751391910260792543693566858410776771319540417882323) * 10 ^ 70 +
        1869168748055297586133679048295451427949955211858957911961816223809402) * 10 ^ 70 +
        4359430160550763835109869569696261506413597018336296121860141351529054) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 109,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (108 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_108_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_109_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (109 + x) *
        remainder6Coefficient1.coeff (109 - (109 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 109 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (109 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (109 - (109 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_109 :
    recurrence4Scalar1Exceptional.coeff 109 =
      -((((276817826864289020140416795234 * 10 ^ 70 +
        0714471430519615267912031102400184519255045073945915929061542901623260) * 10 ^ 70 +
        8944345005340331673739264428377379287623511752825079105912290050730170) * 10 ^ 70 +
        2102664338316139709141479981879411003459148619939248629157214463696456) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 110,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (109 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_109_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_110_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (110 + x) *
        remainder6Coefficient1.coeff (110 - (110 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 110 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (110 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (110 - (110 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_110 :
    recurrence4Scalar1Exceptional.coeff 110 =
      ((((1786979203003072482411447237824 * 10 ^ 70 +
        6421630966095720676661027242976657982374527727092052361096422477843860) * 10 ^ 70 +
        6769542576156754602675920783478434635827581309139741688175013068733945) * 10 ^ 70 +
        4664620042402571178587095490504994845162796960287403805223025004074258) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 111,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (110 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_110_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_111_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (111 + x) *
        remainder6Coefficient1.coeff (111 - (111 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 111 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (111 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (111 - (111 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_111 :
    recurrence4Scalar1Exceptional.coeff 111 =
      -((((10246966486277234582142209221248 * 10 ^ 70 +
        4356362576810610377137248527057055677916175916379966182427221832452571) * 10 ^ 70 +
        1264959283484908852903388963232421256492241597110123060356326739020113) * 10 ^ 70 +
        0752229343596510911471536268044484762195420770712584567742018420434147) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 112,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (111 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_111_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_112_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (112 + x) *
        remainder6Coefficient1.coeff (112 - (112 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 112 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (112 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (112 - (112 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_112 :
    recurrence4Scalar1Exceptional.coeff 112 =
      ((((47333122564242577413966422937362 * 10 ^ 70 +
        1964518068452285394855979374161235437927947837724509637684292571244993) * 10 ^ 70 +
        8448518195806821863749719476372329224142830449221750068795793738810406) * 10 ^ 70 +
        5563127309938445099939071159964282900233224100338635392314047028486220) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 113,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (112 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_112_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_113_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (113 + x) *
        remainder6Coefficient1.coeff (113 - (113 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 113 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (113 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (113 - (113 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_113 :
    recurrence4Scalar1Exceptional.coeff 113 =
      -((((107856718411983004181854864347430 * 10 ^ 70 +
        3330769162425603521973767115355849157766164215481770289835010305104662) * 10 ^ 70 +
        5222313439893986819531474963846588915591113357192795785725680321409174) * 10 ^ 70 +
        5142214828557794777797927300381340825672704396572903932486264078936302) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 114,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (113 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_113_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_114_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (114 + x) *
        remainder6Coefficient1.coeff (114 - (114 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 114 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (114 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (114 - (114 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_114 :
    recurrence4Scalar1Exceptional.coeff 114 =
      -((((1067777570635484589522431101960050 * 10 ^ 70 +
        7244105706299688405385701736303436024996826849342451286792524406322552) * 10 ^ 70 +
        5603450214154985166101455117076730061846202379897394487886542944499295) * 10 ^ 70 +
        5692250120667544695513427185593985834955939093365611789449759225780796) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 115,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (114 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_114_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_115_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (115 + x) *
        remainder6Coefficient1.coeff (115 - (115 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 115 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (115 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (115 - (115 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_115 :
    recurrence4Scalar1Exceptional.coeff 115 =
      ((((20898002292350894116198974203827013 * 10 ^ 70 +
        7866777948953197748156074733224418723596398731107381054134214700403793) * 10 ^ 70 +
        1808606593742024276207931693608936182052081815541525152244431713250718) * 10 ^ 70 +
        9214715686444632030388590872634979408009380093603764049938983371727654) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 116,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (115 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_115_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_116_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (116 + x) *
        remainder6Coefficient1.coeff (116 - (116 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 116 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (116 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (116 - (116 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_116 :
    recurrence4Scalar1Exceptional.coeff 116 =
      -((((235150222764125919465797846913664935 * 10 ^ 70 +
        1990472038064502508489709116936871415965971518222085020268195758079331) * 10 ^ 70 +
        8872613191888543777425977547135845251926035003459029138010017359403348) * 10 ^ 70 +
        2732143824659662060465479264661390101511795252619812428658747393946032) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 117,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (116 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_116_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_117_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (117 + x) *
        remainder6Coefficient1.coeff (117 - (117 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 117 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (117 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (117 - (117 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_117 :
    recurrence4Scalar1Exceptional.coeff 117 =
      ((((2161161550003207262791200915249713042 * 10 ^ 70 +
        3222059253333947168615199941448787369944999322654948672459820999128879) * 10 ^ 70 +
        3779086079822877448947321018412514717615824363804095102832669609459961) * 10 ^ 70 +
        7046699182098052932195986716763533571413397421382235383526562430043641) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 118,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (117 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_117_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_118_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (118 + x) *
        remainder6Coefficient1.coeff (118 - (118 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 118 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (118 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (118 - (118 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_118 :
    recurrence4Scalar1Exceptional.coeff 118 =
      -((((17541454054002358572884799285311030161 * 10 ^ 70 +
        7925723694897435583594479197090665144333516609149609172429527061463487) * 10 ^ 70 +
        4016910695410806408263275508247933043769587099969583322204807806077970) * 10 ^ 70 +
        7256896155210627177170134556900901775472898045199852451646915405341149) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 119,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (118 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_118_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_119_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (119 + x) *
        remainder6Coefficient1.coeff (119 - (119 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 119 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (119 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (119 - (119 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_119 :
    recurrence4Scalar1Exceptional.coeff 119 =
      ((((129126385249592546040866955575176823733 * 10 ^ 70 +
        1535946579379222404281067944907802496451415725684704210958435760746400) * 10 ^ 70 +
        8842495957928337233470689417778847310850226146695026546470463522126879) * 10 ^ 70 +
        8053059499753212340340136409357934737660945233949610395557156683657916) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 120,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (119 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_119_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_120_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (120 + x) *
        remainder6Coefficient1.coeff (120 - (120 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 120 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (120 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (120 - (120 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_120 :
    recurrence4Scalar1Exceptional.coeff 120 =
      -((((867911163241317191282360529479740014839 * 10 ^ 70 +
        8188558798908384233216872379551187837882507396973548738307140095545447) * 10 ^ 70 +
        0348359388745015227721761045376966152777842856061569177231996347645594) * 10 ^ 70 +
        5002679273581400044799260932501630107479666053501789047683031682339043) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 121,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (120 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_120_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_121_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (121 + x) *
        remainder6Coefficient1.coeff (121 - (121 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 121 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (121 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (121 - (121 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_121 :
    recurrence4Scalar1Exceptional.coeff 121 =
      ((((5288890367578804726034163707519280801477 * 10 ^ 70 +
        4708629367438130601786995013380285194991684883961604358754842298512158) * 10 ^ 70 +
        6048525876721666903653171740746769900302073245211690952122011508438543) * 10 ^ 70 +
        9213737850550521511415596816438103432059471169641827109175454447477080) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 122,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (121 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_121_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_122_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (122 + x) *
        remainder6Coefficient1.coeff (122 - (122 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 122 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (122 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (122 - (122 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_122 :
    recurrence4Scalar1Exceptional.coeff 122 =
      -((((28455073988803942921261003381914764497437 * 10 ^ 70 +
        8346937964187917840336805457429173262094702752246679393080812550294549) * 10 ^ 70 +
        9968475617910707764950704850238896990548843317411281454508497450203457) * 10 ^ 70 +
        4505417124127296025744622085651899476996138711757115132708364814402552) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 123,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (122 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_122_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_123_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (123 + x) *
        remainder6Coefficient1.coeff (123 - (123 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 123 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (123 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (123 - (123 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_123 :
    recurrence4Scalar1Exceptional.coeff 123 =
      ((((125233159989801360311524535315819888706117 * 10 ^ 70 +
        4486925607486958891998769794808892557118011022478393757597256966613533) * 10 ^ 70 +
        6559378752823958162105375685476001171396769615664858134604207401911816) * 10 ^ 70 +
        9826660369352530203247583711427305282608430126942443280960841839884490) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 124,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (123 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_123_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_124_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (124 + x) *
        remainder6Coefficient1.coeff (124 - (124 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 124 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (124 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (124 - (124 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_124 :
    recurrence4Scalar1Exceptional.coeff 124 =
      -((((323774597967597042622190421782423803828337 * 10 ^ 70 +
        3157256644669010950467925313200183678603965664495549336431842869624750) * 10 ^ 70 +
        9680061795321743074240918004216078609479100040876245255374163050646425) * 10 ^ 70 +
        1611360596173710738649658994004568968809289367534902701785670171302722) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 125,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (124 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_124_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_125_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (125 + x) *
        remainder6Coefficient1.coeff (125 - (125 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 125 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (125 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (125 - (125 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_125 :
    recurrence4Scalar1Exceptional.coeff 125 =
      -((((1405750483540573042587149024335874485938804 * 10 ^ 70 +
        8258680645222770864581329246730501154355426334428781732118691203104605) * 10 ^ 70 +
        0188300131687071480339155283822009626049637093616418773787838575612317) * 10 ^ 70 +
        7759496983645175172453928873586937875294152548287812324785807935006758) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 126,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (125 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_125_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_126_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (126 + x) *
        remainder6Coefficient1.coeff (126 - (126 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 126 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (126 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (126 - (126 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_126 :
    recurrence4Scalar1Exceptional.coeff 126 =
      ((((31474675070847362606542624244583071317480891 * 10 ^ 70 +
        7188789071486398487260818040016738322140122877769850595497996613460446) * 10 ^ 70 +
        1518159525226045044787124076390757925263495660524919130393181944129946) * 10 ^ 70 +
        0105325238459542216236739907244368359765287054643396380029507156818478) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 127,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (126 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_126_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_127_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (127 + x) *
        remainder6Coefficient1.coeff (127 - (127 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 127 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (127 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (127 - (127 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_127 :
    recurrence4Scalar1Exceptional.coeff 127 =
      -((((329940254562097962094782633444173089712237186 * 10 ^ 70 +
        4271913208836372730664329545068969261166049640536403884319686281283905) * 10 ^ 70 +
        9898163294476456587741763189274222801012146381049204079467285553209353) * 10 ^ 70 +
        7329884698683408300727130000070934457635649408026621134584850689512454) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 128,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (127 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_127_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_128_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (128 + x) *
        remainder6Coefficient1.coeff (128 - (128 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 128 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (128 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (128 - (128 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_128 :
    recurrence4Scalar1Exceptional.coeff 128 =
      ((((2738903954736575214123290762041559754357769733 * 10 ^ 70 +
        7516434665952593480711278891538232448175493345544213786445591292170040) * 10 ^ 70 +
        1613229348257624180842458440290065058042358393622498300598227207322487) * 10 ^ 70 +
        8664303259876837465445670046855634854004498944176762191311735009535777) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 129,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (128 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_128_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_129_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (129 + x) *
        remainder6Coefficient1.coeff (129 - (129 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 129 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (129 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (129 - (129 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_129 :
    recurrence4Scalar1Exceptional.coeff 129 =
      -((((19837447320758828254729651819078871184977923616 * 10 ^ 70 +
        9808178725360151965551599553776454791163404353575798867636781975916011) * 10 ^ 70 +
        5265154736997670372675299368331934368869590139331194338750840868892040) * 10 ^ 70 +
        9981356042799416476841124379945495625642389877023449687018461112724334) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 130,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (129 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_129_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_130_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (130 + x) *
        remainder6Coefficient1.coeff (130 - (130 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 130 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (130 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (130 - (130 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_130 :
    recurrence4Scalar1Exceptional.coeff 130 =
      ((((129365083283932314258500680110581315635407547452 * 10 ^ 70 +
        3254736322553951412288166433562597029745477428298845021229000460009115) * 10 ^ 70 +
        4297099775074555364310502358354388181266543865589931587465617262256766) * 10 ^ 70 +
        8590872520421957723540066282979504491480310867099743492570175117559581) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 131,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (130 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_130_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_131_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (131 + x) *
        remainder6Coefficient1.coeff (131 - (131 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 131 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (131 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (131 - (131 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_131 :
    recurrence4Scalar1Exceptional.coeff 131 =
      -((((765517272934183490220827158186861204633775767591 * 10 ^ 70 +
        4370465127159473003541127666896640392298079767537151875099321557341294) * 10 ^ 70 +
        9990288329010212591300448381040275031933012728627332976051023202696059) * 10 ^ 70 +
        3440211715360602473180464224543417543548683400669328064999759359616289) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 132,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (131 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_131_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_132_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (132 + x) *
        remainder6Coefficient1.coeff (132 - (132 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 132 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (132 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (132 - (132 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_132 :
    recurrence4Scalar1Exceptional.coeff 132 =
      ((((4074285290128914342888465742157289292567460270551 * 10 ^ 70 +
        3535955095514796555212470291356444636498940255357042933493586599391130) * 10 ^ 70 +
        5164257206836547147532348885518619373365489777142274004165421628284949) * 10 ^ 70 +
        4084672838889526397040760417301878052263400602734293874185132606219099) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 133,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (132 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_132_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_133_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (133 + x) *
        remainder6Coefficient1.coeff (133 - (133 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 133 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (133 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (133 - (133 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_133 :
    recurrence4Scalar1Exceptional.coeff 133 =
      -((((18852106120053443483840103196202843586432296975505 * 10 ^ 70 +
        7393475274465377639575010033475782117225553132452740721943781376254493) * 10 ^ 70 +
        4500816507124903396389932594842906507663626399008508549204153313020955) * 10 ^ 70 +
        1074614814243765651677873766115789891040261816858664406516154354205242) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 134,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (133 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_133_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_134_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (134 + x) *
        remainder6Coefficient1.coeff (134 - (134 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 134 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (134 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (134 - (134 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_134 :
    recurrence4Scalar1Exceptional.coeff 134 =
      ((((68130767809577208811330281938720565923904615829610 * 10 ^ 70 +
        6458820157637689823882571683013284256602795233900517740591136936377680) * 10 ^ 70 +
        6289646526794295759935888507153960770710079514631834521019087551136114) * 10 ^ 70 +
        3381357662308549877353264582065201816200932077069743490354097407527685) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 135,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (134 - x)) = _
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
  rw [recurrence4Scalar1Exceptional_coeff_134_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
