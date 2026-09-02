/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB5
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupLeadingSquarePart0Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: LeadingSquare coefficient convolution

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

private theorem recurrence2LeadingSquare_coeff_150_prefix_zero :
    (∑ x ∈ Finset.range 16,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (150 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (150 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_150_suffix_zero :
    (∑ x ∈ Finset.range 16,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (150 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_150 :
    recurrence2LeadingSquare.coeff 150 =
      (((17110797625113 * 10 ^ 70 +
        7803136354220251963079489049286862744914123159981350292869984453567655) * 10 ^ 70 +
        5829840466942300490220856394431217402135911992478764601119107403024203) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 151 = 16 +
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
    rw [show 39 = 23 +
      16 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_150_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_150_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2LeadingSquare_coeff_151_prefix_zero :
    (∑ x ∈ Finset.range 17,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (151 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (151 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_151_suffix_zero :
    (∑ x ∈ Finset.range 17,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (151 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_151 :
    recurrence2LeadingSquare.coeff 151 =
      -(((66674868401816 * 10 ^ 70 +
        2780079362463552910070745305411224731696510162418121923428655029483340) * 10 ^ 70 +
        1588864578536592429664980335202620368235379849800908284035380407939170) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 152 = 17 +
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
    rw [show 39 = 22 +
      17 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_151_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_151_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2LeadingSquare_coeff_152_prefix_zero :
    (∑ x ∈ Finset.range 18,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (152 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (152 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_152_suffix_zero :
    (∑ x ∈ Finset.range 18,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (152 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_152 :
    recurrence2LeadingSquare.coeff 152 =
      (((198060875696329 * 10 ^ 70 +
        6589765158416653692001097551802121479083241208538797376701403628594383) * 10 ^ 70 +
        2656435579946694090560510350834810558591884521562878942718034443015725) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 153 = 18 +
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
    rw [show 39 = 21 +
      18 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_152_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_152_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2LeadingSquare_coeff_153_prefix_zero :
    (∑ x ∈ Finset.range 19,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (153 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (153 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_153_suffix_zero :
    (∑ x ∈ Finset.range 19,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (153 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_153 :
    recurrence2LeadingSquare.coeff 153 =
      -(((506357284447979 * 10 ^ 70 +
        7266226266335547070704491894519187557272627397107753688492538825594723) * 10 ^ 70 +
        5429423630655691878173884915481560860585309622910647776995701255468672) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 154 = 19 +
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
    rw [show 39 = 20 +
      19 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_153_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_153_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2LeadingSquare_coeff_154_prefix_zero :
    (∑ x ∈ Finset.range 20,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (154 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (154 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_154_suffix_zero :
    (∑ x ∈ Finset.range 20,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (154 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_154 :
    recurrence2LeadingSquare.coeff 154 =
      (((1165410133137277 * 10 ^ 70 +
        4254076600929588374492559981798635841383448187877256917822597838044166) * 10 ^ 70 +
        6729098040554143795841370633239333555458964240461848678909808066764451) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 155 = 20 +
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
    rw [show 39 = 19 +
      20 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_154_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_154_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2LeadingSquare_coeff_155_prefix_zero :
    (∑ x ∈ Finset.range 21,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (155 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (155 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_155_suffix_zero :
    (∑ x ∈ Finset.range 21,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (155 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_155 :
    recurrence2LeadingSquare.coeff 155 =
      -(((2469290847431323 * 10 ^ 70 +
        8713867468967484736279227852078564289909363216931331125088591615794132) * 10 ^ 70 +
        9588956860963621905305399520838740959187031649581350967675857619794060) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 156 = 21 +
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
    rw [show 39 = 18 +
      21 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_155_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_155_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2LeadingSquare_coeff_156_prefix_zero :
    (∑ x ∈ Finset.range 22,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (156 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (156 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_156_suffix_zero :
    (∑ x ∈ Finset.range 22,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (156 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_156 :
    recurrence2LeadingSquare.coeff 156 =
      (((4879812377420622 * 10 ^ 70 +
        3644614782040771001510051075364991829949051071761523100610787810143118) * 10 ^ 70 +
        2686699142055411151022356709030087513369399429586959711266753881473745) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 157 = 22 +
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
    rw [show 39 = 17 +
      22 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_156_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_156_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2LeadingSquare_coeff_157_prefix_zero :
    (∑ x ∈ Finset.range 23,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (157 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (157 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_157_suffix_zero :
    (∑ x ∈ Finset.range 23,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (157 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_157 :
    recurrence2LeadingSquare.coeff 157 =
      -(((9070595625898303 * 10 ^ 70 +
        3697253838118346009299964451172117819602497619593858222937748327347676) * 10 ^ 70 +
        2773850950255377997119479093829362039842677350913619468548156812185072) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 158 = 23 +
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
    rw [show 39 = 16 +
      23 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_157_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_157_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2LeadingSquare_coeff_158_prefix_zero :
    (∑ x ∈ Finset.range 24,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (158 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (158 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_158_suffix_zero :
    (∑ x ∈ Finset.range 24,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (158 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_158 :
    recurrence2LeadingSquare.coeff 158 =
      (((15951979756759907 * 10 ^ 70 +
        6432915155663492747524921130371108100472709421689907528406078127051213) * 10 ^ 70 +
        5396348184049152367414231099604443365189081496813614071019907637984586) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 159 = 24 +
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
    rw [show 39 = 15 +
      24 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_158_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_158_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2LeadingSquare_coeff_159_prefix_zero :
    (∑ x ∈ Finset.range 25,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (159 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (159 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_159_suffix_zero :
    (∑ x ∈ Finset.range 25,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (159 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_159 :
    recurrence2LeadingSquare.coeff 159 =
      -(((26656267954113195 * 10 ^ 70 +
        4944863148428924785234347156599594967499391278940227502498735232985139) * 10 ^ 70 +
        9835924272667324858098516530858505528745478416779535096686640719270424) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 160 = 25 +
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
    rw [show 39 = 14 +
      25 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_159_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_159_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2LeadingSquare_coeff_160_prefix_zero :
    (∑ x ∈ Finset.range 26,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (160 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (160 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_160_suffix_zero :
    (∑ x ∈ Finset.range 26,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (160 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_160 :
    recurrence2LeadingSquare.coeff 160 =
      (((42462260821889358 * 10 ^ 70 +
        8048599722423182140246951731972230594691315745124558405957631249531439) * 10 ^ 70 +
        5038564117316556201463988024047381329283541521026475993742603490194503) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 161 = 26 +
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
    rw [show 39 = 13 +
      26 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_160_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_160_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2LeadingSquare_coeff_161_prefix_zero :
    (∑ x ∈ Finset.range 27,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (161 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (161 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_161_suffix_zero :
    (∑ x ∈ Finset.range 27,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (161 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_161 :
    recurrence2LeadingSquare.coeff 161 =
      -(((64644522565907105 * 10 ^ 70 +
        0111420052572303362650081732526273212546528981068750102730847447024483) * 10 ^ 70 +
        2570365848984397006613083626401423394405718030886319893093130205281468) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 162 = 27 +
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
    rw [show 39 = 12 +
      27 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_161_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_161_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2LeadingSquare_coeff_162_prefix_zero :
    (∑ x ∈ Finset.range 28,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (162 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (162 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_162_suffix_zero :
    (∑ x ∈ Finset.range 28,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (162 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_162 :
    recurrence2LeadingSquare.coeff 162 =
      (((94247720756585141 * 10 ^ 70 +
        0548285100009841693011212051484520245736045033294196874316990910754201) * 10 ^ 70 +
        5262019637358391591584994035311244930957584445448007293190482704564818) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 163 = 28 +
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
    rw [show 39 = 11 +
      28 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_162_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_162_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2LeadingSquare_coeff_163_prefix_zero :
    (∑ x ∈ Finset.range 29,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (163 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (163 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_163_suffix_zero :
    (∑ x ∈ Finset.range 29,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (163 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_163 :
    recurrence2LeadingSquare.coeff 163 =
      -(((131808321179580348 * 10 ^ 70 +
        0604944564749018442532190391953172386838444005303647405194582100059049) * 10 ^ 70 +
        7387758481400842812399883716274346062903767782233273284541330747720588) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 164 = 29 +
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
    rw [show 39 = 10 +
      29 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_163_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_163_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2LeadingSquare_coeff_164_prefix_zero :
    (∑ x ∈ Finset.range 30,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (164 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (164 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_164_suffix_zero :
    (∑ x ∈ Finset.range 30,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (164 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_164 :
    recurrence2LeadingSquare.coeff 164 =
      (((177070139740146117 * 10 ^ 70 +
        1554026460212924309907777448460316389740463010088882821481194503468618) * 10 ^ 70 +
        4419993593040215228563970056858241850171804641252218772784154267519459) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 165 = 30 +
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
    rw [show 39 = 9 +
      30 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_164_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_164_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2LeadingSquare_coeff_165_prefix_zero :
    (∑ x ∈ Finset.range 31,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (165 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (165 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_165_suffix_zero :
    (∑ x ∈ Finset.range 31,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (165 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_165 :
    recurrence2LeadingSquare.coeff 165 =
      -(((228759172998877039 * 10 ^ 70 +
        8957622966484034698299725454532066241757746197491602581983815710846928) * 10 ^ 70 +
        4212605247694170406643710454898916068696553488384538942928627239511346) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 166 = 31 +
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
    rw [show 39 = 8 +
      31 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_165_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_165_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2LeadingSquare_coeff_166_prefix_zero :
    (∑ x ∈ Finset.range 32,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (166 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (166 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_166_suffix_zero :
    (∑ x ∈ Finset.range 32,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (166 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_166 :
    recurrence2LeadingSquare.coeff 166 =
      (((284488434923996265 * 10 ^ 70 +
        5128043614739638670305918058857397206827631310008557768153014225224471) * 10 ^ 70 +
        1711201472649932121974464793620071438065985543537001633720722506388751) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 167 = 32 +
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
    rw [show 39 = 7 +
      32 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_166_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_166_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2LeadingSquare_coeff_167_prefix_zero :
    (∑ x ∈ Finset.range 33,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (167 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (167 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_167_suffix_zero :
    (∑ x ∈ Finset.range 33,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (167 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_167 :
    recurrence2LeadingSquare.coeff 167 =
      -(((340849291862578963 * 10 ^ 70 +
        7155602375680749089901391124930806354539425205508765670628640410791474) * 10 ^ 70 +
        9597305233737252030007447888147002018615372587989731726619136893766366) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 168 = 33 +
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
    rw [show 39 = 6 +
      33 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_167_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_167_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2LeadingSquare_coeff_168_prefix_zero :
    (∑ x ∈ Finset.range 34,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (168 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (168 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_168_suffix_zero :
    (∑ x ∈ Finset.range 34,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (168 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_168 :
    recurrence2LeadingSquare.coeff 168 =
      (((393711498839999002 * 10 ^ 70 +
        5393468418425137843442496546308349874889374918003367882552183379234511) * 10 ^ 70 +
        5609887109249082143816362742604121271938235745793486089778167750181137) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 169 = 34 +
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
    rw [show 39 = 5 +
      34 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_168_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_168_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2LeadingSquare_coeff_169_prefix_zero :
    (∑ x ∈ Finset.range 35,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (169 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (169 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_169_suffix_zero :
    (∑ x ∈ Finset.range 35,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (169 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_169 :
    recurrence2LeadingSquare.coeff 169 =
      -(((438706250280023447 * 10 ^ 70 +
        9315794830626408856848736537991752662825518948016803581536909139826117) * 10 ^ 70 +
        8581019990857780546016833787773256626389536685424577245175639942336556) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 170 = 35 +
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
    rw [show 39 = 4 +
      35 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_169_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_169_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2LeadingSquare_coeff_170_prefix_zero :
    (∑ x ∈ Finset.range 36,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (170 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (170 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_170_suffix_zero :
    (∑ x ∈ Finset.range 36,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (170 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_170 :
    recurrence2LeadingSquare.coeff 170 =
      (((471817508450118668 * 10 ^ 70 +
        8745253953030173641668037184780281979186812458942290824944423874472464) * 10 ^ 70 +
        7886743605591826207328841403183397006353700064896626772598765239672698) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 171 = 36 +
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
    rw [show 39 = 3 +
      36 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_170_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_170_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2LeadingSquare_coeff_171_prefix_zero :
    (∑ x ∈ Finset.range 37,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (171 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (171 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_171_suffix_zero :
    (∑ x ∈ Finset.range 37,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (171 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_171 :
    recurrence2LeadingSquare.coeff 171 =
      -(((489971517758549278 * 10 ^ 70 +
        6295474434813443592506175798300171995771936980048572122345792741895010) * 10 ^ 70 +
        3913535860528468525691334815474861941888824661099241671630626952929432) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 172 = 37 +
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
    rw [show 39 = 2 +
      37 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_171_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_171_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2LeadingSquare_coeff_172_prefix_zero :
    (∑ x ∈ Finset.range 38,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (172 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (172 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_172_suffix_zero :
    (∑ x ∈ Finset.range 38,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (172 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_172 :
    recurrence2LeadingSquare.coeff 172 =
      (((491504943529613846 * 10 ^ 70 +
        2803873268348120657864562966765284189311016073710450305399959256645427) * 10 ^ 70 +
        0991100563216025934415222199271179540237047213928760840050022475309811) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 173 = 38 +
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
    rw [show 39 = 1 +
      38 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_172_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_172_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2LeadingSquare_coeff_173_prefix_zero :
    (∑ x ∈ Finset.range 39,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (173 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (173 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_173_suffix_zero :
    (∑ x ∈ Finset.range 39,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (173 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_173 :
    recurrence2LeadingSquare.coeff 173 =
      -(((476413376328820565 * 10 ^ 70 +
        4042469131841676794869069612724255999970421608891566798415264690237296) * 10 ^ 70 +
        2398931059481738777350530102745520264482143350656882841261344363547470) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 174 = 39 +
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
  rw [recurrence2LeadingSquare_coeff_173_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_173_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2LeadingSquare_coeff_174_prefix_zero :
    (∑ x ∈ Finset.range 40,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (174 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (174 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_174_suffix_zero :
    (∑ x ∈ Finset.range 40,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (174 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_174 :
    recurrence2LeadingSquare.coeff 174 =
      (((446329348460158462 * 10 ^ 70 +
        7017496237428318676686082338228054122385295926409965679363715265397592) * 10 ^ 70 +
        1273223444086736593138428696663046794972828737255290532410281368882084) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 175 = 40 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 31 +
      40 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_174_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_174_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2LeadingSquare_coeff_175_prefix_zero :
    (∑ x ∈ Finset.range 41,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (175 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (175 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_175_suffix_zero :
    (∑ x ∈ Finset.range 41,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (175 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_175 :
    recurrence2LeadingSquare.coeff 175 =
      -(((404239505203883525 * 10 ^ 70 +
        6435442552323175229710529313163177784154028033998804829736420734722638) * 10 ^ 70 +
        1409079299455487425486106842335187912230967145414987424055419824900504) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 176 = 41 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 30 +
      41 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_175_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_175_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2LeadingSquare_coeff_176_prefix_zero :
    (∑ x ∈ Finset.range 42,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (176 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (176 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_176_suffix_zero :
    (∑ x ∈ Finset.range 42,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (176 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_176 :
    recurrence2LeadingSquare.coeff 176 =
      (((354007117760415995 * 10 ^ 70 +
        7961277015278161165684734226316587483101461751545100832655887903289497) * 10 ^ 70 +
        7103532007056140053337783774977501322396522260210464715953942127484309) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 177 = 42 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 29 +
      42 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_176_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_176_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2LeadingSquare_coeff_177_prefix_zero :
    (∑ x ∈ Finset.range 43,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (177 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (177 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_177_suffix_zero :
    (∑ x ∈ Finset.range 43,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (177 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_177 :
    recurrence2LeadingSquare.coeff 177 =
      -(((299803394967670974 * 10 ^ 70 +
        0731134628448428581492622479629012682519448067942537007391478556474969) * 10 ^ 70 +
        9390868963521169687848019932663884126327098269706443998244357066199664) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 178 = 43 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 28 +
      43 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_177_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_177_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2LeadingSquare_coeff_178_prefix_zero :
    (∑ x ∈ Finset.range 44,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (178 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (178 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_178_suffix_zero :
    (∑ x ∈ Finset.range 44,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (178 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_178 :
    recurrence2LeadingSquare.coeff 178 =
      (((245560379963959955 * 10 ^ 70 +
        1630039560963338965902733824437674845094935232806199810786598908730067) * 10 ^ 70 +
        1199408169235597941825791339381784997360594031112557543465143179794980) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 179 = 44 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 27 +
      44 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_178_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_178_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2LeadingSquare_coeff_179_prefix_zero :
    (∑ x ∈ Finset.range 45,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (179 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (179 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_179_suffix_zero :
    (∑ x ∈ Finset.range 45,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (179 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_179 :
    recurrence2LeadingSquare.coeff 179 =
      -(((194539891360412406 * 10 ^ 70 +
        1672881843698526975899647274178080393502587504889897914797525385262616) * 10 ^ 70 +
        1989812595126109606091476490710889908069559092410174517951776211379634) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 180 = 45 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 26 +
      45 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_179_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_179_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2LeadingSquare_coeff_180_prefix_zero :
    (∑ x ∈ Finset.range 46,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (180 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (180 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_180_suffix_zero :
    (∑ x ∈ Finset.range 46,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (180 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_180 :
    recurrence2LeadingSquare.coeff 180 =
      (((149075226496705352 * 10 ^ 70 +
        7447493202646368848088827347027378472594998010919183995090600643410940) * 10 ^ 70 +
        7917994324435433751563420526168734763501909156511646178951800096618502) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 181 = 46 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 25 +
      46 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_180_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_180_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2LeadingSquare_coeff_181_prefix_zero :
    (∑ x ∈ Finset.range 47,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (181 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (181 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_181_suffix_zero :
    (∑ x ∈ Finset.range 47,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (181 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_181 :
    recurrence2LeadingSquare.coeff 181 =
      -(((110497799112994452 * 10 ^ 70 +
        2241872135013172588106467042053021511395087613359186421138353682304729) * 10 ^ 70 +
        2957239961105335319098725497687399336830934799041198689585023074137522) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 182 = 47 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 24 +
      47 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_181_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_181_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2LeadingSquare_coeff_182_prefix_zero :
    (∑ x ∈ Finset.range 48,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (182 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (182 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_182_suffix_zero :
    (∑ x ∈ Finset.range 48,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (182 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_182 :
    recurrence2LeadingSquare.coeff 182 =
      (((79221978279861330 * 10 ^ 70 +
        7821982073305994635169150382389827528287945534585378626815338686052800) * 10 ^ 70 +
        7239513874891218983877668671197068361431328212821452696414127369971537) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 183 = 48 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 23 +
      48 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_182_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_182_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2LeadingSquare_coeff_183_prefix_zero :
    (∑ x ∈ Finset.range 49,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (183 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (183 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_183_suffix_zero :
    (∑ x ∈ Finset.range 49,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (183 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_183 :
    recurrence2LeadingSquare.coeff 183 =
      -(((54936669060384169 * 10 ^ 70 +
        8689556286648118449588688578599546910934586405961542073678281132594542) * 10 ^ 70 +
        9375916457808369323965357804043602811761526102072119606907368968070982) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 184 = 49 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 22 +
      49 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_183_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_183_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2LeadingSquare_coeff_184_prefix_zero :
    (∑ x ∈ Finset.range 50,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (184 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (184 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_184_suffix_zero :
    (∑ x ∈ Finset.range 50,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (184 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_184 :
    recurrence2LeadingSquare.coeff 184 =
      (((36844502955873192 * 10 ^ 70 +
        1701264772888659446594928845644464083576611927249761749998029708521050) * 10 ^ 70 +
        2027904934455929589468100528723010062423538226424594106877839557571598) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 185 = 50 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 21 +
      50 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_184_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_184_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2LeadingSquare_coeff_185_prefix_zero :
    (∑ x ∈ Finset.range 51,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (185 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (185 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_185_suffix_zero :
    (∑ x ∈ Finset.range 51,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (185 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_185 :
    recurrence2LeadingSquare.coeff 185 =
      -(((23896522935918248 * 10 ^ 70 +
        0136884398156507136156508710381830256462634378529393120402453090829310) * 10 ^ 70 +
        3058977628029452723993133566461525569047648063439653182893123531632036) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 186 = 51 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 20 +
      51 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_185_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_185_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
