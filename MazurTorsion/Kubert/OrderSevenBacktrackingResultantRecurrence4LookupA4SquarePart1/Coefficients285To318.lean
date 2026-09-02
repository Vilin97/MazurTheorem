/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupA4
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupA4SquarePart1Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: A4Square coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4A4_coeff_100
  recurrence4A4_coeff_101
  recurrence4A4_coeff_102
  recurrence4A4_coeff_103
  recurrence4A4_coeff_104
  recurrence4A4_coeff_105
  recurrence4A4_coeff_106
  recurrence4A4_coeff_107
  recurrence4A4_coeff_108
  recurrence4A4_coeff_109
  recurrence4A4_coeff_110
  recurrence4A4_coeff_111
  recurrence4A4_coeff_112
  recurrence4A4_coeff_113
  recurrence4A4_coeff_114
  recurrence4A4_coeff_115
  recurrence4A4_coeff_116
  recurrence4A4_coeff_117
  recurrence4A4_coeff_118
  recurrence4A4_coeff_119
  recurrence4A4_coeff_120
  recurrence4A4_coeff_121
  recurrence4A4_coeff_122
  recurrence4A4_coeff_123
  recurrence4A4_coeff_124
  recurrence4A4_coeff_125
  recurrence4A4_coeff_126
  recurrence4A4_coeff_127
  recurrence4A4_coeff_128
  recurrence4A4_coeff_129
  recurrence4A4_coeff_130
  recurrence4A4_coeff_131
  recurrence4A4_coeff_132
  recurrence4A4_coeff_133
  recurrence4A4_coeff_134
  recurrence4A4_coeff_135
  recurrence4A4_coeff_136
  recurrence4A4_coeff_137
  recurrence4A4_coeff_138
  recurrence4A4_coeff_139
  recurrence4A4_coeff_140
  recurrence4A4_coeff_141
  recurrence4A4_coeff_142
  recurrence4A4_coeff_143
  recurrence4A4_coeff_144
  recurrence4A4_coeff_145
  recurrence4A4_coeff_146
  recurrence4A4_coeff_147
  recurrence4A4_coeff_148
  recurrence4A4_coeff_149
  recurrence4A4_coeff_150
  recurrence4A4_coeff_151
  recurrence4A4_coeff_152
  recurrence4A4_coeff_153
  recurrence4A4_coeff_154
  recurrence4A4_coeff_155
  recurrence4A4_coeff_156
  recurrence4A4_coeff_157
  recurrence4A4_coeff_158
  recurrence4A4_coeff_159
  recurrence4A4_coeff_160
  recurrence4A4_coeff_161
  recurrence4A4_coeff_162
  recurrence4A4_coeff_163

attribute [local simp]
  recurrence4A4_coeff_164
  recurrence4A4_coeff_165
  recurrence4A4_coeff_166
  recurrence4A4_coeff_167
  recurrence4A4_coeff_168
  recurrence4A4_coeff_169
  recurrence4A4_coeff_170
  recurrence4A4_coeff_171
  recurrence4A4_coeff_172
  recurrence4A4_coeff_173
  recurrence4A4_coeff_174
  recurrence4A4_coeff_175
  recurrence4A4_coeff_176
  recurrence4A4_coeff_177
  recurrence4A4_coeff_178
  recurrence4A4_coeff_44
  recurrence4A4_coeff_45
  recurrence4A4_coeff_46
  recurrence4A4_coeff_47
  recurrence4A4_coeff_48
  recurrence4A4_coeff_49
  recurrence4A4_coeff_50
  recurrence4A4_coeff_51
  recurrence4A4_coeff_52
  recurrence4A4_coeff_53
  recurrence4A4_coeff_54
  recurrence4A4_coeff_55
  recurrence4A4_coeff_56
  recurrence4A4_coeff_57
  recurrence4A4_coeff_58
  recurrence4A4_coeff_59
  recurrence4A4_coeff_60
  recurrence4A4_coeff_61
  recurrence4A4_coeff_62
  recurrence4A4_coeff_63
  recurrence4A4_coeff_64
  recurrence4A4_coeff_65
  recurrence4A4_coeff_66
  recurrence4A4_coeff_67
  recurrence4A4_coeff_68
  recurrence4A4_coeff_69
  recurrence4A4_coeff_70
  recurrence4A4_coeff_71
  recurrence4A4_coeff_72
  recurrence4A4_coeff_73
  recurrence4A4_coeff_74
  recurrence4A4_coeff_75
  recurrence4A4_coeff_76
  recurrence4A4_coeff_77
  recurrence4A4_coeff_78
  recurrence4A4_coeff_79
  recurrence4A4_coeff_80
  recurrence4A4_coeff_81
  recurrence4A4_coeff_82
  recurrence4A4_coeff_83
  recurrence4A4_coeff_84
  recurrence4A4_coeff_85
  recurrence4A4_coeff_86
  recurrence4A4_coeff_87
  recurrence4A4_coeff_88
  recurrence4A4_coeff_89
  recurrence4A4_coeff_90
  recurrence4A4_coeff_91
  recurrence4A4_coeff_92

attribute [local simp]
  recurrence4A4_coeff_93
  recurrence4A4_coeff_94
  recurrence4A4_coeff_95
  recurrence4A4_coeff_96
  recurrence4A4_coeff_97
  recurrence4A4_coeff_98
  recurrence4A4_coeff_99

private theorem recurrence4A4Square_coeff_285_prefix_zero :
    (∑ x ∈ Finset.range 107,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (285 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (285 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_285_suffix_zero :
    (∑ x ∈ Finset.range 107,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (285 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_285 :
    recurrence4A4Square.coeff 285 =
      (((21777206040412501571009884 * 10 ^ 70 +
        0969651319487524744429562674967610382132393581272445349599178328491552) * 10 ^ 70 +
        9727094744424260786050448426409146392759802863926578717746473950184730) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 286,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (285 - x)) = _
  rw [show 286 = 107 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 8 +
      107 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_285_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_285_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_286_prefix_zero :
    (∑ x ∈ Finset.range 108,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (286 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (286 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_286_suffix_zero :
    (∑ x ∈ Finset.range 108,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (286 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_286 :
    recurrence4A4Square.coeff 286 =
      -(((6282245401999463467947066 * 10 ^ 70 +
        7676595977764372743577399585446417579443782876089808000741249836460012) * 10 ^ 70 +
        6204741472435866634219743642794343153069293546418534357304116231411779) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 287,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (286 - x)) = _
  rw [show 287 = 108 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 7 +
      108 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_286_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_286_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_287_prefix_zero :
    (∑ x ∈ Finset.range 109,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (287 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (287 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_287_suffix_zero :
    (∑ x ∈ Finset.range 109,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (287 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_287 :
    recurrence4A4Square.coeff 287 =
      (((1565872030506002041183273 * 10 ^ 70 +
        7357535539436967650234607777976061312880031181968574106634082189460116) * 10 ^ 70 +
        0900046207062454755311394255680795772553268624419876963308493216571522) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 288,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (287 - x)) = _
  rw [show 288 = 109 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 6 +
      109 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_287_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_287_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_288_prefix_zero :
    (∑ x ∈ Finset.range 110,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (288 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (288 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_288_suffix_zero :
    (∑ x ∈ Finset.range 110,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (288 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_288 :
    recurrence4A4Square.coeff 288 =
      -(((322150821676978679784095 * 10 ^ 70 +
        0819960812902620188964243962069833462165579309923193913309926785158678) * 10 ^ 70 +
        9104082130167434130022869224579824488264903633804482563631615376839898) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 289,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (288 - x)) = _
  rw [show 289 = 110 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 5 +
      110 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_288_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_288_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_289_prefix_zero :
    (∑ x ∈ Finset.range 111,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (289 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (289 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_289_suffix_zero :
    (∑ x ∈ Finset.range 111,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (289 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_289 :
    recurrence4A4Square.coeff 289 =
      (((46071146333463005964446 * 10 ^ 70 +
        9162549778480230263835662511377590423751641117024923383402728126566593) * 10 ^ 70 +
        2031844081583209224921184221052305366244177194062680786903256445827616) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 290,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (289 - x)) = _
  rw [show 290 = 111 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 4 +
      111 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_289_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_289_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_290_prefix_zero :
    (∑ x ∈ Finset.range 112,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (290 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (290 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_290_suffix_zero :
    (∑ x ∈ Finset.range 112,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (290 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_290 :
    recurrence4A4Square.coeff 290 =
      (((302202667574793733035 * 10 ^ 70 +
        8323098292397408006015556950458803968633931687153961168185205180599838) * 10 ^ 70 +
        8960560507835226585702518724080698597695052641248470342715195658077085) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 291,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (290 - x)) = _
  rw [show 291 = 112 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 3 +
      112 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_290_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_290_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_291_prefix_zero :
    (∑ x ∈ Finset.range 113,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (291 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (291 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_291_suffix_zero :
    (∑ x ∈ Finset.range 113,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (291 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_291 :
    recurrence4A4Square.coeff 291 =
      -(((3315103901976073446412 * 10 ^ 70 +
        3683154539774139131337736389108791342268133012767839682101126368859979) * 10 ^ 70 +
        8326848689060153106178395307869136734971935411026362391094876330578130) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 292,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (291 - x)) = _
  rw [show 292 = 113 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 2 +
      113 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_291_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_291_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_292_prefix_zero :
    (∑ x ∈ Finset.range 114,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (292 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (292 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_292_suffix_zero :
    (∑ x ∈ Finset.range 114,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (292 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_292 :
    recurrence4A4Square.coeff 292 =
      (((1549828601732233873707 * 10 ^ 70 +
        3737095268956499644088204980343862469148577590367581267852953200209709) * 10 ^ 70 +
        9786618474287443231912871025939045360968639687533291520016362657884892) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 293,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (292 - x)) = _
  rw [show 293 = 114 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 1 +
      114 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_292_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_292_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_293_prefix_zero :
    (∑ x ∈ Finset.range 115,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (293 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (293 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_293_suffix_zero :
    (∑ x ∈ Finset.range 115,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (293 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_293 :
    recurrence4A4Square.coeff 293 =
      -(((509153632317609389550 * 10 ^ 70 +
        9578501634179824909363666958971463029791197887481318307804953280278938) * 10 ^ 70 +
        5626981319694313576998166055329254170438009517247925558979329560422846) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 294,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (293 - x)) = _
  rw [show 294 = 115 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_293_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_293_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_294_prefix_zero :
    (∑ x ∈ Finset.range 116,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (294 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (294 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_294_suffix_zero :
    (∑ x ∈ Finset.range 116,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (294 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_294 :
    recurrence4A4Square.coeff 294 =
      (((137656697645048750820 * 10 ^ 70 +
        3296281016857395923142839091940858857207307330275991415259341401386011) * 10 ^ 70 +
        5401998717538147190839858436082546025907397895028210812682933726749590) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 295,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (294 - x)) = _
  rw [show 295 = 116 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 31 +
      116 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_294_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_294_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_295_prefix_zero :
    (∑ x ∈ Finset.range 117,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (295 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (295 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_295_suffix_zero :
    (∑ x ∈ Finset.range 117,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (295 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_295 :
    recurrence4A4Square.coeff 295 =
      -(((31957636707014271125 * 10 ^ 70 +
        8806394653016640092887149263951413087418785822051820677756899045398548) * 10 ^ 70 +
        1340337872780908338782641609418103862363974136061789330822256283848346) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 296,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (295 - x)) = _
  rw [show 296 = 117 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 30 +
      117 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_295_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_295_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_296_prefix_zero :
    (∑ x ∈ Finset.range 118,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (296 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (296 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_296_suffix_zero :
    (∑ x ∈ Finset.range 118,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (296 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_296 :
    recurrence4A4Square.coeff 296 =
      (((6419626183081064926 * 10 ^ 70 +
        8330917103802702107227454530032925718281454397367072359120770770198331) * 10 ^ 70 +
        2207012495703181209570999250179593848732387377535556920816492937112478) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 297,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (296 - x)) = _
  rw [show 297 = 118 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 29 +
      118 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_296_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_296_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_297_prefix_zero :
    (∑ x ∈ Finset.range 119,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (297 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (297 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_297_suffix_zero :
    (∑ x ∈ Finset.range 119,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (297 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_297 :
    recurrence4A4Square.coeff 297 =
      -(((1098382631599958837 * 10 ^ 70 +
        4133138797451060951265707392989858754918120998366785876215747045214670) * 10 ^ 70 +
        3366515588590124916918117079262464083290602690292189888631813576166428) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 298,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (297 - x)) = _
  rw [show 298 = 119 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 28 +
      119 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_297_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_297_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_298_prefix_zero :
    (∑ x ∈ Finset.range 120,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (298 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (298 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_298_suffix_zero :
    (∑ x ∈ Finset.range 120,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (298 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_298 :
    recurrence4A4Square.coeff 298 =
      (((151665883292851376 * 10 ^ 70 +
        0983516564889559245016812722721312027465185703549790241068509640321804) * 10 ^ 70 +
        0462549939158447572779735367488208570496247677701192067370743074735121) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 299,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (298 - x)) = _
  rw [show 299 = 120 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 27 +
      120 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_298_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_298_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_299_prefix_zero :
    (∑ x ∈ Finset.range 121,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (299 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (299 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_299_suffix_zero :
    (∑ x ∈ Finset.range 121,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (299 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_299 :
    recurrence4A4Square.coeff 299 =
      -(((13966088814000733 * 10 ^ 70 +
        8951877765300769068239879401935644995946223063390523882568239439433286) * 10 ^ 70 +
        0155338608400611903251427039548594730610074884328949994693985861602440) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 300,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (299 - x)) = _
  rw [show 300 = 121 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 26 +
      121 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_299_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_299_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_300_prefix_zero :
    (∑ x ∈ Finset.range 122,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (300 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (300 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_300_suffix_zero :
    (∑ x ∈ Finset.range 122,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (300 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_300 :
    recurrence4A4Square.coeff 300 =
      -(((194303110837143 * 10 ^ 70 +
        0370324584042228380417809284979431263206832145986359758819284784474489) * 10 ^ 70 +
        6439507314699302088450653362492506666870557567020383020457372188474570) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 301,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (300 - x)) = _
  rw [show 301 = 122 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 25 +
      122 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_300_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_300_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_301_prefix_zero :
    (∑ x ∈ Finset.range 123,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (301 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (301 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_301_suffix_zero :
    (∑ x ∈ Finset.range 123,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (301 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_301 :
    recurrence4A4Square.coeff 301 =
      (((442531672456016 * 10 ^ 70 +
        1781540147770041103398702491254853635162323509212998228314656699464320) * 10 ^ 70 +
        9607586336069753277494151865646785255691918337312881551776564529401742) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 302,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (301 - x)) = _
  rw [show 302 = 123 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 24 +
      123 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_301_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_301_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_302_prefix_zero :
    (∑ x ∈ Finset.range 124,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (302 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (302 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_302_suffix_zero :
    (∑ x ∈ Finset.range 124,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (302 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_302 :
    recurrence4A4Square.coeff 302 =
      -(((119053610657022 * 10 ^ 70 +
        9413244323022609373492624447758286213774016173523724809631105869721011) * 10 ^ 70 +
        0995357173392185218871954892665123850902610358274910047215170927509962) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 303,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (302 - x)) = _
  rw [show 303 = 124 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 23 +
      124 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_302_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_302_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_303_prefix_zero :
    (∑ x ∈ Finset.range 125,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (303 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (303 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_303_suffix_zero :
    (∑ x ∈ Finset.range 125,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (303 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_303 :
    recurrence4A4Square.coeff 303 =
      (((21233326834382 * 10 ^ 70 +
        6096360970245377407446149296024062043734653637586253512514047357158908) * 10 ^ 70 +
        1166538274006522553728986048359174012064342573779234091177566051929834) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 304,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (303 - x)) = _
  rw [show 304 = 125 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 22 +
      125 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_303_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_303_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_304_prefix_zero :
    (∑ x ∈ Finset.range 126,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (304 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (304 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_304_suffix_zero :
    (∑ x ∈ Finset.range 126,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (304 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_304 :
    recurrence4A4Square.coeff 304 =
      -(((2758343932465 * 10 ^ 70 +
        4391523411915180169451865721127133134012946759146746778758456108279374) * 10 ^ 70 +
        2186305315094526166730861831235736427802355794337951602202696204634500) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 305,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (304 - x)) = _
  rw [show 305 = 126 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 21 +
      126 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_304_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_304_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_305_prefix_zero :
    (∑ x ∈ Finset.range 127,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (305 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (305 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_305_suffix_zero :
    (∑ x ∈ Finset.range 127,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (305 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_305 :
    recurrence4A4Square.coeff 305 =
      (((229800221984 * 10 ^ 70 +
        8710784408831528825917312498947761130395043306628871449563027152118838) * 10 ^ 70 +
        7961609982417370329583200229899541608072560413452284966547369875068184) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 306,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (305 - x)) = _
  rw [show 306 = 127 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 20 +
      127 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_305_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_305_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_306_prefix_zero :
    (∑ x ∈ Finset.range 128,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (306 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (306 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_306_suffix_zero :
    (∑ x ∈ Finset.range 128,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (306 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_306 :
    recurrence4A4Square.coeff 306 =
      -(((84861671 * 10 ^ 70 +
        2532554170953936111592731996952837672077330469563853494613013220576816) * 10 ^ 70 +
        5592182897295581266056154886054119061738053058318944883706975956499764) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 307,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (306 - x)) = _
  rw [show 307 = 128 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 19 +
      128 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_306_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_306_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_307_prefix_zero :
    (∑ x ∈ Finset.range 129,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (307 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (307 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_307_suffix_zero :
    (∑ x ∈ Finset.range 129,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (307 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_307 :
    recurrence4A4Square.coeff 307 =
      -(((4065857125 * 10 ^ 70 +
        4657084157447331699829710289503909268326375426580901443627875199785951) * 10 ^ 70 +
        3949484472010609806491221180186218645032382546341525895924729317472128) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 308,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (307 - x)) = _
  rw [show 308 = 129 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 18 +
      129 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_307_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_307_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_308_prefix_zero :
    (∑ x ∈ Finset.range 130,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (308 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (308 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_308_suffix_zero :
    (∑ x ∈ Finset.range 130,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (308 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_308 :
    recurrence4A4Square.coeff 308 =
      (((848271663 * 10 ^ 70 +
        8363069907702317713667128384423913143053678464218212051314446558567366) * 10 ^ 70 +
        2796958879529511965587802403136953910970841288108259515982882910010917) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 309,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (308 - x)) = _
  rw [show 309 = 130 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 17 +
      130 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_308_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_308_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_309_prefix_zero :
    (∑ x ∈ Finset.range 131,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (309 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (309 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_309_suffix_zero :
    (∑ x ∈ Finset.range 131,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (309 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_309 :
    recurrence4A4Square.coeff 309 =
      -(((106257205 * 10 ^ 70 +
        6473425914499850748251679390054692898495152797716962041074305710996664) * 10 ^ 70 +
        4235159552525773306845259175935884195491223631827880714738544567145990) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 310,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (309 - x)) = _
  rw [show 310 = 131 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 16 +
      131 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_309_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_309_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_310_prefix_zero :
    (∑ x ∈ Finset.range 132,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (310 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (310 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_310_suffix_zero :
    (∑ x ∈ Finset.range 132,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (310 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_310 :
    recurrence4A4Square.coeff 310 =
      (((8210183 * 10 ^ 70 +
        0138327709542615612973274991327315867333741067517319667653813271617951) * 10 ^ 70 +
        5714447514808595063284669780206521909293366965974047286541510258183395) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 311,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (310 - x)) = _
  rw [show 311 = 132 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 15 +
      132 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_310_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_310_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_311_prefix_zero :
    (∑ x ∈ Finset.range 133,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (311 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (311 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_311_suffix_zero :
    (∑ x ∈ Finset.range 133,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (311 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_311 :
    recurrence4A4Square.coeff 311 =
      -(((138086 * 10 ^ 70 +
        9680824709228582326933911945107449323103834781748554729595191632870614) * 10 ^ 70 +
        1214880184609389847298889589998369470865196092106471795868447691294346) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 312,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (311 - x)) = _
  rw [show 312 = 133 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 14 +
      133 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_311_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_311_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_312_prefix_zero :
    (∑ x ∈ Finset.range 134,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (312 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (312 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_312_suffix_zero :
    (∑ x ∈ Finset.range 134,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (312 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_312 :
    recurrence4A4Square.coeff 312 =
      -(((64330 * 10 ^ 70 +
        0201280008034259098144153440709949341744414979656634428533234326503823) * 10 ^ 70 +
        8694047885737812107871887848301660178344148327317336637086262382186192) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 313,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (312 - x)) = _
  rw [show 313 = 134 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 13 +
      134 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_312_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_312_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_313_prefix_zero :
    (∑ x ∈ Finset.range 135,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (313 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (313 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_313_suffix_zero :
    (∑ x ∈ Finset.range 135,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (313 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_313 :
    recurrence4A4Square.coeff 313 =
      (((10402 * 10 ^ 70 +
        3888984065548121896766415452441251068229738829032384790898234619306639) * 10 ^ 70 +
        8405755292329656783368914014943329242753533536770600461141044996235682) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 314,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (313 - x)) = _
  rw [show 314 = 135 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 12 +
      135 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_313_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_313_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_314_prefix_zero :
    (∑ x ∈ Finset.range 136,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (314 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (314 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_314_suffix_zero :
    (∑ x ∈ Finset.range 136,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (314 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_314 :
    recurrence4A4Square.coeff 314 =
      -(((806 * 10 ^ 70 +
        1013533348543984196462262269957632941893469344168333219168186900617719) * 10 ^ 70 +
        4188990750183892040305521695007537858122581653953719754928521864539374) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 315,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (314 - x)) = _
  rw [show 315 = 136 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 11 +
      136 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_314_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_314_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_315_prefix_zero :
    (∑ x ∈ Finset.range 137,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (315 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (315 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_315_suffix_zero :
    (∑ x ∈ Finset.range 137,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (315 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_315 :
    recurrence4A4Square.coeff 315 =
      (((16 * 10 ^ 70 +
        3865834708706676119720753761527595150638483863732896384852364501329795) * 10 ^ 70 +
        4497178988636476047624757444148647927550222758905223024757234220383398) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 316,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (315 - x)) = _
  rw [show 316 = 137 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 10 +
      137 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_315_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_315_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_316_prefix_zero :
    (∑ x ∈ Finset.range 138,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (316 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (316 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_316_suffix_zero :
    (∑ x ∈ Finset.range 138,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (316 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_316 :
    recurrence4A4Square.coeff 316 =
      (((3 * 10 ^ 70 +
        7364593617292319025539021830657334773106909659294692301886712379204503) * 10 ^ 70 +
        2526711621785702454202530419690745442447382334617581378103558623078431) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 317,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (316 - x)) = _
  rw [show 317 = 138 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 9 +
      138 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_316_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_316_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_317_prefix_zero :
    (∑ x ∈ Finset.range 139,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (317 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (317 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_317_suffix_zero :
    (∑ x ∈ Finset.range 139,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (317 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_317 :
    recurrence4A4Square.coeff 317 =
      -((4618624762702026193193615047055988864261021927287933485866708587510280 * 10 ^ 70 +
        3761849584615686503976663428613253692674920829073067809738588560188090) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 318,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (317 - x)) = _
  rw [show 318 = 139 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 8 +
      139 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_317_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_317_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_318_prefix_zero :
    (∑ x ∈ Finset.range 140,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (318 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (318 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_318_suffix_zero :
    (∑ x ∈ Finset.range 140,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (318 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_318 :
    recurrence4A4Square.coeff 318 =
      ((197489283828704116835029462949195685111890198643363778298206006614758 * 10 ^ 70 +
        7784078112620700070309030458775966469698694101004573341223396494309057) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 319,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (318 - x)) = _
  rw [show 319 = 140 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 7 +
      140 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_318_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_318_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
