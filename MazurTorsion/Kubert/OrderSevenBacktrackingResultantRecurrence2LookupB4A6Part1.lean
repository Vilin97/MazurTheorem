/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB4
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupA6
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: B4A6 coefficient convolution

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence2B4_coeff_0
  recurrence2B4_coeff_1
  recurrence2B4_coeff_2
  recurrence2B4_coeff_3
  recurrence2B4_coeff_4
  recurrence2B4_coeff_5
  recurrence2B4_coeff_6
  recurrence2B4_coeff_7
  recurrence2B4_coeff_8
  recurrence2B4_coeff_9
  recurrence2B4_coeff_10
  recurrence2B4_coeff_11
  recurrence2B4_coeff_12
  recurrence2B4_coeff_13
  recurrence2B4_coeff_14
  recurrence2B4_coeff_15
  recurrence2B4_coeff_16
  recurrence2B4_coeff_17
  recurrence2B4_coeff_18
  recurrence2B4_coeff_19
  recurrence2B4_coeff_20
  recurrence2B4_coeff_21
  recurrence2B4_coeff_22
  recurrence2B4_coeff_23
  recurrence2B4_coeff_24
  recurrence2B4_coeff_25
  recurrence2B4_coeff_26
  recurrence2B4_coeff_27
  recurrence2B4_coeff_28
  recurrence2B4_coeff_29
  recurrence2B4_coeff_30
  recurrence2B4_coeff_31
  recurrence2B4_coeff_32
  recurrence2B4_coeff_33
  recurrence2B4_coeff_34
  recurrence2B4_coeff_35
  recurrence2B4_coeff_36
  recurrence2B4_coeff_37
  recurrence2B4_coeff_38
  recurrence2B4_coeff_39
  recurrence2B4_coeff_40
  recurrence2B4_coeff_41
  recurrence2B4_coeff_42
  recurrence2B4_coeff_43
  recurrence2B4_coeff_44
  recurrence2B4_coeff_45
  recurrence2B4_coeff_46
  recurrence2B4_coeff_47
  recurrence2B4_coeff_48
  recurrence2B4_coeff_49
  recurrence2B4_coeff_50
  recurrence2B4_coeff_51
  recurrence2B4_coeff_52
  recurrence2B4_coeff_53
  recurrence2B4_coeff_54
  recurrence2B4_coeff_55
  recurrence2B4_coeff_56
  recurrence2B4_coeff_57
  recurrence2B4_coeff_58
  recurrence2B4_coeff_59
  recurrence2B4_coeff_60
  recurrence2B4_coeff_61
  recurrence2B4_coeff_62
  recurrence2B4_coeff_63
  recurrence2B4_coeff_64
  recurrence2B4_coeff_65
  recurrence2B4_coeff_66
  recurrence2B4_coeff_67
  recurrence2B4_coeff_68
  recurrence2B4_coeff_69
  recurrence2B4_coeff_70
  recurrence2B4_coeff_71
  recurrence2B4_coeff_72
  recurrence2B4_coeff_73
  recurrence2B4_coeff_74
  recurrence2B4_coeff_75
  recurrence2B4_coeff_76
  recurrence2B4_coeff_77
  recurrence2B4_coeff_78
  recurrence2B4_coeff_79
  recurrence2B4_coeff_80
  recurrence2B4_coeff_81
  recurrence2B4_coeff_82
  recurrence2B4_coeff_83
  recurrence2B4_coeff_84
  recurrence2B4_coeff_85
  recurrence2B4_coeff_86
  recurrence2B4_coeff_87
  recurrence2B4_coeff_88
  recurrence2B4_coeff_89
  recurrence2B4_coeff_90
  recurrence2B4_coeff_91
  recurrence2B4_coeff_92
  recurrence2B4_coeff_93
  recurrence2B4_coeff_94
  recurrence2B4_coeff_95
  recurrence2B4_coeff_96
  recurrence2B4_coeff_97
  recurrence2B4_coeff_98
  recurrence2B4_coeff_99
  recurrence2B4_coeff_100
  recurrence2B4_coeff_101
  recurrence2B4_coeff_102
  recurrence2B4_coeff_103
  recurrence2B4_coeff_104
  recurrence2B4_coeff_105
  recurrence2B4_coeff_106
  recurrence2B4_coeff_107
  recurrence2B4_coeff_108
  recurrence2B4_coeff_109
  recurrence2B4_coeff_110
  recurrence2B4_coeff_111
  recurrence2B4_coeff_112
  recurrence2B4_coeff_113
  recurrence2B4_coeff_114
  recurrence2B4_coeff_115
  recurrence2B4_coeff_116
  recurrence2B4_coeff_117
  recurrence2B4_coeff_118
  recurrence2B4_coeff_119
  recurrence2B4_coeff_120
  recurrence2B4_coeff_121
  recurrence2B4_coeff_122
  recurrence2B4_coeff_123
  recurrence2B4_coeff_124
  recurrence2B4_coeff_125
  recurrence2B4_coeff_126
  recurrence2B4_coeff_127
  recurrence2B4_coeff_128
  recurrence2B4_coeff_129
  recurrence2B4_coeff_130
  recurrence2B4_coeff_131
  recurrence2B4_coeff_132
  recurrence2B4_coeff_133
  recurrence2B4_coeff_134
  recurrence2B4_coeff_135
  recurrence2B4_coeff_136
  recurrence2B4_coeff_137
  recurrence2B4_coeff_138
  recurrence2A6_coeff_0
  recurrence2A6_coeff_1
  recurrence2A6_coeff_2
  recurrence2A6_coeff_3
  recurrence2A6_coeff_4
  recurrence2A6_coeff_5
  recurrence2A6_coeff_6
  recurrence2A6_coeff_7
  recurrence2A6_coeff_8
  recurrence2A6_coeff_9
  recurrence2A6_coeff_10
  recurrence2A6_coeff_11
  recurrence2A6_coeff_12
  recurrence2A6_coeff_13
  recurrence2A6_coeff_14
  recurrence2A6_coeff_15
  recurrence2A6_coeff_16
  recurrence2A6_coeff_17
  recurrence2A6_coeff_18
  recurrence2A6_coeff_19
  recurrence2A6_coeff_20
  recurrence2A6_coeff_21
  recurrence2A6_coeff_22
  recurrence2A6_coeff_23
  recurrence2A6_coeff_24
  recurrence2A6_coeff_25
  recurrence2A6_coeff_26
  recurrence2A6_coeff_27
  recurrence2A6_coeff_28
  recurrence2A6_coeff_29
  recurrence2A6_coeff_30
  recurrence2A6_coeff_31
  recurrence2A6_coeff_32
  recurrence2A6_coeff_33
  recurrence2A6_coeff_34
  recurrence2A6_coeff_35
  recurrence2A6_coeff_36
  recurrence2A6_coeff_37
  recurrence2A6_coeff_38
  recurrence2A6_coeff_39
  recurrence2A6_coeff_40
  recurrence2A6_coeff_41
  recurrence2A6_coeff_42
  recurrence2A6_coeff_43
  recurrence2A6_coeff_44
  recurrence2A6_coeff_45
  recurrence2A6_coeff_46
  recurrence2A6_coeff_47
  recurrence2A6_coeff_48
  recurrence2A6_coeff_49
  recurrence2A6_coeff_50
  recurrence2A6_coeff_51
  recurrence2A6_coeff_52
  recurrence2A6_coeff_53
  recurrence2A6_coeff_54
  recurrence2A6_coeff_55
  recurrence2A6_coeff_56
  recurrence2A6_coeff_57
  recurrence2A6_coeff_58
  recurrence2A6_coeff_59
  recurrence2A6_coeff_60
  recurrence2A6_coeff_61
  recurrence2A6_coeff_62
  recurrence2A6_coeff_63
  recurrence2A6_coeff_64
  recurrence2A6_coeff_65
  recurrence2A6_coeff_66
  recurrence2A6_coeff_67
  recurrence2A6_coeff_68
  recurrence2A6_coeff_69
  recurrence2A6_coeff_70
  recurrence2A6_coeff_71
  recurrence2A6_coeff_72
  recurrence2A6_coeff_73
  recurrence2A6_coeff_74
  recurrence2A6_coeff_75
  recurrence2A6_coeff_76
  recurrence2A6_coeff_77
  recurrence2A6_coeff_78
  recurrence2A6_coeff_79
  recurrence2A6_coeff_80
  recurrence2A6_coeff_81
  recurrence2A6_coeff_82
  recurrence2A6_coeff_83
  recurrence2A6_coeff_84
  recurrence2A6_coeff_85
  recurrence2A6_coeff_86
  recurrence2A6_coeff_87
  recurrence2A6_coeff_88
  recurrence2A6_coeff_89
  recurrence2A6_coeff_90
  recurrence2A6_coeff_91
  recurrence2A6_coeff_92
  recurrence2A6_coeff_93
  recurrence2A6_coeff_94
  recurrence2A6_coeff_95

private theorem recurrence2B4A6_coeff_224_prefix_zero :
    (∑ x ∈ Finset.range 129,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (224 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (224 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_224_suffix_zero :
    (∑ x ∈ Finset.range 86,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (224 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_224 :
    recurrence2B4A6.coeff 224 =
      (19715573706913481332375156059984820926622748964910259122 : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 225 = 129 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 10 +
      86 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_224_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_224_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_225_prefix_zero :
    (∑ x ∈ Finset.range 130,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (225 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (225 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_225_suffix_zero :
    (∑ x ∈ Finset.range 87,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (225 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_225 :
    recurrence2B4A6.coeff 225 =
      (-49219436219500557630486811808146028270351414370123099 : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 226 = 130 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 9 +
      87 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_225_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_225_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_226_prefix_zero :
    (∑ x ∈ Finset.range 131,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (226 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (226 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_226_suffix_zero :
    (∑ x ∈ Finset.range 88,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (226 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_226 :
    recurrence2B4A6.coeff 226 =
      (4933202531700162411118574472565904492270830826583 : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 227 = 131 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 8 +
      88 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_226_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_226_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_227_prefix_zero :
    (∑ x ∈ Finset.range 132,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (227 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (227 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_227_suffix_zero :
    (∑ x ∈ Finset.range 89,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (227 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_227 :
    recurrence2B4A6.coeff 227 =
      (360304337667999354141051538783132905768407797 : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 228 = 132 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 7 +
      89 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_227_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_227_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_228_prefix_zero :
    (∑ x ∈ Finset.range 133,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (228 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (228 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_228_suffix_zero :
    (∑ x ∈ Finset.range 90,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (228 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_228 :
    recurrence2B4A6.coeff 228 =
      (-19865755923574628531227232192393850048199 : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 229 = 133 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 6 +
      90 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_228_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_228_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_229_prefix_zero :
    (∑ x ∈ Finset.range 134,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (229 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (229 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_229_suffix_zero :
    (∑ x ∈ Finset.range 91,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (229 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_229 :
    recurrence2B4A6.coeff 229 =
      (53284904898157868586233070890225574 : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 230 = 134 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 5 +
      91 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_229_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_229_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_230_prefix_zero :
    (∑ x ∈ Finset.range 135,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (230 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (230 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_230_suffix_zero :
    (∑ x ∈ Finset.range 92,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (230 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_230 :
    recurrence2B4A6.coeff 230 =
      (356642044832950146976124570938 : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 231 = 135 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 4 +
      92 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_230_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_230_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_231_prefix_zero :
    (∑ x ∈ Finset.range 136,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (231 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (231 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_231_suffix_zero :
    (∑ x ∈ Finset.range 93,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (231 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_231 :
    recurrence2B4A6.coeff 231 =
      (-176047813390480004487987 : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 232 = 136 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 3 +
      93 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_231_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_231_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_232_prefix_zero :
    (∑ x ∈ Finset.range 137,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (232 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (232 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_232_suffix_zero :
    (∑ x ∈ Finset.range 94,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (232 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_232 :
    recurrence2B4A6.coeff 232 =
      (219350432717800 : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 233 = 137 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 2 +
      94 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_232_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_232_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_233_prefix_zero :
    (∑ x ∈ Finset.range 138,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (233 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (233 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_233_suffix_zero :
    (∑ x ∈ Finset.range 95,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (233 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_233 :
    recurrence2B4A6.coeff 233 =
      (794588 : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 234 = 138 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 1 +
      95 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_233_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_233_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
