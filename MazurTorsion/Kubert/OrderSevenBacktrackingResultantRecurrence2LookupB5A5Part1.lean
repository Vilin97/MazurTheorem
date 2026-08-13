/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB5
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupA5
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB5A5Part1Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: B5A5 coefficient convolution

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence2B5_coeff_0
  recurrence2B5_coeff_1
  recurrence2B5_coeff_2
  recurrence2B5_coeff_3
  recurrence2B5_coeff_4
  recurrence2B5_coeff_5
  recurrence2B5_coeff_6
  recurrence2B5_coeff_7
  recurrence2B5_coeff_8
  recurrence2B5_coeff_9
  recurrence2B5_coeff_10
  recurrence2B5_coeff_11
  recurrence2B5_coeff_12
  recurrence2B5_coeff_13
  recurrence2B5_coeff_14
  recurrence2B5_coeff_15
  recurrence2B5_coeff_16
  recurrence2B5_coeff_17
  recurrence2B5_coeff_18
  recurrence2B5_coeff_19
  recurrence2B5_coeff_20
  recurrence2B5_coeff_21
  recurrence2B5_coeff_22
  recurrence2B5_coeff_23
  recurrence2B5_coeff_24
  recurrence2B5_coeff_25
  recurrence2B5_coeff_26
  recurrence2B5_coeff_27
  recurrence2B5_coeff_28
  recurrence2B5_coeff_29
  recurrence2B5_coeff_30
  recurrence2B5_coeff_31
  recurrence2B5_coeff_32
  recurrence2B5_coeff_33
  recurrence2B5_coeff_34
  recurrence2B5_coeff_35
  recurrence2B5_coeff_36
  recurrence2B5_coeff_37
  recurrence2B5_coeff_38
  recurrence2B5_coeff_39
  recurrence2B5_coeff_40
  recurrence2B5_coeff_41
  recurrence2B5_coeff_42
  recurrence2B5_coeff_43
  recurrence2B5_coeff_44
  recurrence2B5_coeff_45
  recurrence2B5_coeff_46
  recurrence2B5_coeff_47
  recurrence2B5_coeff_48
  recurrence2B5_coeff_49
  recurrence2B5_coeff_50
  recurrence2B5_coeff_51
  recurrence2B5_coeff_52
  recurrence2B5_coeff_53
  recurrence2B5_coeff_54
  recurrence2B5_coeff_55
  recurrence2B5_coeff_56
  recurrence2B5_coeff_57
  recurrence2B5_coeff_58
  recurrence2B5_coeff_59
  recurrence2B5_coeff_60
  recurrence2B5_coeff_61
  recurrence2B5_coeff_62
  recurrence2B5_coeff_63
  recurrence2B5_coeff_64
  recurrence2B5_coeff_65
  recurrence2B5_coeff_66
  recurrence2B5_coeff_67
  recurrence2B5_coeff_68
  recurrence2B5_coeff_69
  recurrence2B5_coeff_70
  recurrence2B5_coeff_71
  recurrence2B5_coeff_72
  recurrence2B5_coeff_73
  recurrence2B5_coeff_74
  recurrence2B5_coeff_75
  recurrence2B5_coeff_76
  recurrence2B5_coeff_77
  recurrence2B5_coeff_78
  recurrence2B5_coeff_79
  recurrence2B5_coeff_80
  recurrence2B5_coeff_81
  recurrence2B5_coeff_82
  recurrence2B5_coeff_83
  recurrence2B5_coeff_84
  recurrence2B5_coeff_85
  recurrence2B5_coeff_86
  recurrence2B5_coeff_87
  recurrence2B5_coeff_88
  recurrence2B5_coeff_89
  recurrence2B5_coeff_90
  recurrence2B5_coeff_91
  recurrence2B5_coeff_92
  recurrence2B5_coeff_93
  recurrence2B5_coeff_94
  recurrence2B5_coeff_95
  recurrence2B5_coeff_96
  recurrence2B5_coeff_97
  recurrence2B5_coeff_98
  recurrence2B5_coeff_99
  recurrence2B5_coeff_100
  recurrence2B5_coeff_101
  recurrence2B5_coeff_102
  recurrence2B5_coeff_103
  recurrence2B5_coeff_104
  recurrence2B5_coeff_105
  recurrence2B5_coeff_106
  recurrence2B5_coeff_107
  recurrence2B5_coeff_108
  recurrence2B5_coeff_109
  recurrence2B5_coeff_110
  recurrence2B5_coeff_111
  recurrence2B5_coeff_112
  recurrence2B5_coeff_113
  recurrence2B5_coeff_114
  recurrence2B5_coeff_115
  recurrence2B5_coeff_116
  recurrence2B5_coeff_117
  recurrence2B5_coeff_118
  recurrence2B5_coeff_119
  recurrence2B5_coeff_120
  recurrence2B5_coeff_121
  recurrence2B5_coeff_122
  recurrence2B5_coeff_123
  recurrence2B5_coeff_124
  recurrence2B5_coeff_125
  recurrence2B5_coeff_126
  recurrence2B5_coeff_127
  recurrence2B5_coeff_128
  recurrence2B5_coeff_129
  recurrence2B5_coeff_130
  recurrence2B5_coeff_131
  recurrence2B5_coeff_132
  recurrence2B5_coeff_133
  recurrence2B5_coeff_134
  recurrence2A5_coeff_0
  recurrence2A5_coeff_1
  recurrence2A5_coeff_2
  recurrence2A5_coeff_3
  recurrence2A5_coeff_4
  recurrence2A5_coeff_5
  recurrence2A5_coeff_6
  recurrence2A5_coeff_7
  recurrence2A5_coeff_8
  recurrence2A5_coeff_9
  recurrence2A5_coeff_10
  recurrence2A5_coeff_11
  recurrence2A5_coeff_12
  recurrence2A5_coeff_13
  recurrence2A5_coeff_14
  recurrence2A5_coeff_15
  recurrence2A5_coeff_16
  recurrence2A5_coeff_17
  recurrence2A5_coeff_18
  recurrence2A5_coeff_19
  recurrence2A5_coeff_20
  recurrence2A5_coeff_21
  recurrence2A5_coeff_22
  recurrence2A5_coeff_23
  recurrence2A5_coeff_24
  recurrence2A5_coeff_25
  recurrence2A5_coeff_26
  recurrence2A5_coeff_27
  recurrence2A5_coeff_28
  recurrence2A5_coeff_29
  recurrence2A5_coeff_30
  recurrence2A5_coeff_31
  recurrence2A5_coeff_32
  recurrence2A5_coeff_33
  recurrence2A5_coeff_34
  recurrence2A5_coeff_35
  recurrence2A5_coeff_36
  recurrence2A5_coeff_37
  recurrence2A5_coeff_38
  recurrence2A5_coeff_39
  recurrence2A5_coeff_40
  recurrence2A5_coeff_41
  recurrence2A5_coeff_42
  recurrence2A5_coeff_43
  recurrence2A5_coeff_44
  recurrence2A5_coeff_45
  recurrence2A5_coeff_46
  recurrence2A5_coeff_47
  recurrence2A5_coeff_48
  recurrence2A5_coeff_49
  recurrence2A5_coeff_50
  recurrence2A5_coeff_51
  recurrence2A5_coeff_52
  recurrence2A5_coeff_53
  recurrence2A5_coeff_54
  recurrence2A5_coeff_55
  recurrence2A5_coeff_56
  recurrence2A5_coeff_57
  recurrence2A5_coeff_58
  recurrence2A5_coeff_59
  recurrence2A5_coeff_60
  recurrence2A5_coeff_61
  recurrence2A5_coeff_62
  recurrence2A5_coeff_63
  recurrence2A5_coeff_64
  recurrence2A5_coeff_65
  recurrence2A5_coeff_66
  recurrence2A5_coeff_67
  recurrence2A5_coeff_68
  recurrence2A5_coeff_69
  recurrence2A5_coeff_70
  recurrence2A5_coeff_71
  recurrence2A5_coeff_72
  recurrence2A5_coeff_73
  recurrence2A5_coeff_74
  recurrence2A5_coeff_75
  recurrence2A5_coeff_76
  recurrence2A5_coeff_77
  recurrence2A5_coeff_78
  recurrence2A5_coeff_79
  recurrence2A5_coeff_80
  recurrence2A5_coeff_81
  recurrence2A5_coeff_82
  recurrence2A5_coeff_83
  recurrence2A5_coeff_84
  recurrence2A5_coeff_85
  recurrence2A5_coeff_86
  recurrence2A5_coeff_87
  recurrence2A5_coeff_88
  recurrence2A5_coeff_89
  recurrence2A5_coeff_90
  recurrence2A5_coeff_91
  recurrence2A5_coeff_92
  recurrence2A5_coeff_93
  recurrence2A5_coeff_94
  recurrence2A5_coeff_95
  recurrence2A5_coeff_96
  recurrence2A5_coeff_97
  recurrence2A5_coeff_98

private theorem recurrence2B5A5_coeff_221_prefix_zero :
    (∑ x ∈ Finset.range 123,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (221 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (221 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_221_suffix_zero :
    (∑ x ∈ Finset.range 87,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (221 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_221 :
    recurrence2B5A5.coeff 221 =
      (-171593573110694647551588714980045556964041186178511235068837238280 : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 222 = 123 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 12 +
      87 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_221_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_221_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_222_prefix_zero :
    (∑ x ∈ Finset.range 124,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (222 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (222 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_222_suffix_zero :
    (∑ x ∈ Finset.range 88,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (222 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_222 :
    recurrence2B5A5.coeff 222 =
      (-6854648218170304330236652376774529482330304716114497263953856 : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 223 = 124 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 11 +
      88 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_222_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_222_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_223_prefix_zero :
    (∑ x ∈ Finset.range 125,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (223 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (223 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_223_suffix_zero :
    (∑ x ∈ Finset.range 89,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (223 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_223 :
    recurrence2B5A5.coeff 223 =
      (202197923375703081614685193711601903255601382071879255530540 : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 224 = 125 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 10 +
      89 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_223_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_223_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_224_prefix_zero :
    (∑ x ∈ Finset.range 126,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (224 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (224 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_224_suffix_zero :
    (∑ x ∈ Finset.range 90,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (224 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_224 :
    recurrence2B5A5.coeff 224 =
      (-67033740414698297311363511796623727268702788092632095286 : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 225 = 126 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 9 +
      90 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_224_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_224_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_225_prefix_zero :
    (∑ x ∈ Finset.range 127,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (225 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (225 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_225_suffix_zero :
    (∑ x ∈ Finset.range 91,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (225 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_225 :
    recurrence2B5A5.coeff 225 =
      (-22735057220515599869815873147903470113705811159315298 : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 226 = 127 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 8 +
      91 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_225_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_225_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_226_prefix_zero :
    (∑ x ∈ Finset.range 128,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (226 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (226 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_226_suffix_zero :
    (∑ x ∈ Finset.range 92,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (226 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_226 :
    recurrence2B5A5.coeff 226 =
      (6008743886930501378846285008199429693053739006829 : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 227 = 128 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 7 +
      92 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_226_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_226_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_227_prefix_zero :
    (∑ x ∈ Finset.range 129,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (227 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (227 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_227_suffix_zero :
    (∑ x ∈ Finset.range 93,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (227 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_227 :
    recurrence2B5A5.coeff 227 =
      (-39852917686914495886837773420878798153061090 : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 228 = 129 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 6 +
      93 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_227_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_227_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_228_prefix_zero :
    (∑ x ∈ Finset.range 130,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (228 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (228 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_228_suffix_zero :
    (∑ x ∈ Finset.range 94,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (228 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_228 :
    recurrence2B5A5.coeff 228 =
      (-11840295095498590559973233318430170408632 : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 229 = 130 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 5 +
      94 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_228_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_228_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_229_prefix_zero :
    (∑ x ∈ Finset.range 131,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (229 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (229 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_229_suffix_zero :
    (∑ x ∈ Finset.range 95,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (229 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_229 :
    recurrence2B5A5.coeff 229 =
      (95326495687294354814350859275007811 : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 230 = 131 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 4 +
      95 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_229_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_229_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_230_prefix_zero :
    (∑ x ∈ Finset.range 132,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (230 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (230 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_230_suffix_zero :
    (∑ x ∈ Finset.range 96,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (230 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_230 :
    recurrence2B5A5.coeff 230 =
      (77652505695459674612092165662 : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 231 = 132 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 3 +
      96 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_230_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_230_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_231_prefix_zero :
    (∑ x ∈ Finset.range 133,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (231 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (231 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_231_suffix_zero :
    (∑ x ∈ Finset.range 97,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (231 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_231 :
    recurrence2B5A5.coeff 231 =
      (-115186270234295645118569 : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 232 = 133 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 2 +
      97 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_231_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_231_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_232_prefix_zero :
    (∑ x ∈ Finset.range 134,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (232 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (232 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_232_suffix_zero :
    (∑ x ∈ Finset.range 98,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (232 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_232 :
    recurrence2B5A5.coeff 232 =
      (785155589424736 : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 233 = 134 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 1 +
      98 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_232_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_232_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
