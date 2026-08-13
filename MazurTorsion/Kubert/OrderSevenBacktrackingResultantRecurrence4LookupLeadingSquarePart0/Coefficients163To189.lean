/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB3
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupLeadingSquarePart0Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: LeadingSquare coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4B3_coeff_0
  recurrence4B3_coeff_1
  recurrence4B3_coeff_10
  recurrence4B3_coeff_100
  recurrence4B3_coeff_101
  recurrence4B3_coeff_102
  recurrence4B3_coeff_103
  recurrence4B3_coeff_104
  recurrence4B3_coeff_105
  recurrence4B3_coeff_106
  recurrence4B3_coeff_107
  recurrence4B3_coeff_108
  recurrence4B3_coeff_109
  recurrence4B3_coeff_11
  recurrence4B3_coeff_110
  recurrence4B3_coeff_111
  recurrence4B3_coeff_112
  recurrence4B3_coeff_113
  recurrence4B3_coeff_114
  recurrence4B3_coeff_115
  recurrence4B3_coeff_116
  recurrence4B3_coeff_117
  recurrence4B3_coeff_118
  recurrence4B3_coeff_119
  recurrence4B3_coeff_12
  recurrence4B3_coeff_120
  recurrence4B3_coeff_121
  recurrence4B3_coeff_122
  recurrence4B3_coeff_123
  recurrence4B3_coeff_124
  recurrence4B3_coeff_125
  recurrence4B3_coeff_126
  recurrence4B3_coeff_127
  recurrence4B3_coeff_128
  recurrence4B3_coeff_129
  recurrence4B3_coeff_13
  recurrence4B3_coeff_130
  recurrence4B3_coeff_131
  recurrence4B3_coeff_132
  recurrence4B3_coeff_133
  recurrence4B3_coeff_134
  recurrence4B3_coeff_135
  recurrence4B3_coeff_136
  recurrence4B3_coeff_137
  recurrence4B3_coeff_138
  recurrence4B3_coeff_139
  recurrence4B3_coeff_14
  recurrence4B3_coeff_140
  recurrence4B3_coeff_141
  recurrence4B3_coeff_142
  recurrence4B3_coeff_143
  recurrence4B3_coeff_144
  recurrence4B3_coeff_145
  recurrence4B3_coeff_146
  recurrence4B3_coeff_147
  recurrence4B3_coeff_148
  recurrence4B3_coeff_149
  recurrence4B3_coeff_15
  recurrence4B3_coeff_150
  recurrence4B3_coeff_151
  recurrence4B3_coeff_152
  recurrence4B3_coeff_153
  recurrence4B3_coeff_154
  recurrence4B3_coeff_155

attribute [local simp]
  recurrence4B3_coeff_156
  recurrence4B3_coeff_157
  recurrence4B3_coeff_158
  recurrence4B3_coeff_159
  recurrence4B3_coeff_16
  recurrence4B3_coeff_160
  recurrence4B3_coeff_161
  recurrence4B3_coeff_162
  recurrence4B3_coeff_163
  recurrence4B3_coeff_164
  recurrence4B3_coeff_17
  recurrence4B3_coeff_18
  recurrence4B3_coeff_19
  recurrence4B3_coeff_2
  recurrence4B3_coeff_20
  recurrence4B3_coeff_21
  recurrence4B3_coeff_22
  recurrence4B3_coeff_23
  recurrence4B3_coeff_24
  recurrence4B3_coeff_25
  recurrence4B3_coeff_26
  recurrence4B3_coeff_27
  recurrence4B3_coeff_28
  recurrence4B3_coeff_29
  recurrence4B3_coeff_3
  recurrence4B3_coeff_30
  recurrence4B3_coeff_31
  recurrence4B3_coeff_32
  recurrence4B3_coeff_33
  recurrence4B3_coeff_34
  recurrence4B3_coeff_35
  recurrence4B3_coeff_36
  recurrence4B3_coeff_37
  recurrence4B3_coeff_38
  recurrence4B3_coeff_39
  recurrence4B3_coeff_4
  recurrence4B3_coeff_40
  recurrence4B3_coeff_41
  recurrence4B3_coeff_42
  recurrence4B3_coeff_43
  recurrence4B3_coeff_44
  recurrence4B3_coeff_45
  recurrence4B3_coeff_46
  recurrence4B3_coeff_47
  recurrence4B3_coeff_48
  recurrence4B3_coeff_49
  recurrence4B3_coeff_5
  recurrence4B3_coeff_50
  recurrence4B3_coeff_51
  recurrence4B3_coeff_52
  recurrence4B3_coeff_53
  recurrence4B3_coeff_54
  recurrence4B3_coeff_55
  recurrence4B3_coeff_56
  recurrence4B3_coeff_57
  recurrence4B3_coeff_58
  recurrence4B3_coeff_59
  recurrence4B3_coeff_6
  recurrence4B3_coeff_60
  recurrence4B3_coeff_61
  recurrence4B3_coeff_62
  recurrence4B3_coeff_63
  recurrence4B3_coeff_64
  recurrence4B3_coeff_65

attribute [local simp]
  recurrence4B3_coeff_66
  recurrence4B3_coeff_67
  recurrence4B3_coeff_68
  recurrence4B3_coeff_69
  recurrence4B3_coeff_7
  recurrence4B3_coeff_70
  recurrence4B3_coeff_71
  recurrence4B3_coeff_72
  recurrence4B3_coeff_73
  recurrence4B3_coeff_74
  recurrence4B3_coeff_75
  recurrence4B3_coeff_76
  recurrence4B3_coeff_77
  recurrence4B3_coeff_78
  recurrence4B3_coeff_79
  recurrence4B3_coeff_8
  recurrence4B3_coeff_80
  recurrence4B3_coeff_81
  recurrence4B3_coeff_82
  recurrence4B3_coeff_83
  recurrence4B3_coeff_84
  recurrence4B3_coeff_85
  recurrence4B3_coeff_86
  recurrence4B3_coeff_87
  recurrence4B3_coeff_88
  recurrence4B3_coeff_89
  recurrence4B3_coeff_9
  recurrence4B3_coeff_90
  recurrence4B3_coeff_91
  recurrence4B3_coeff_92
  recurrence4B3_coeff_93
  recurrence4B3_coeff_94
  recurrence4B3_coeff_95
  recurrence4B3_coeff_96
  recurrence4B3_coeff_97
  recurrence4B3_coeff_98
  recurrence4B3_coeff_99

theorem recurrence4LeadingSquare_coeff_163 :
    recurrence4LeadingSquare.coeff 163 =
      (((837318115446979635495087694903284866101427140478437938463293417537 * 10 ^ 70 +
        2712858652617545113402551206760491108443038654489997639747755827677143) * 10 ^ 70 +
        6167806090240560858299282513939504919804964531592790073412518566328190) : ℚ) := by
  unfold recurrence4LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 164,
    remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (163 - x)) = _
  rw [show 164 = 0 +
    164 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 164 = 32 +
      132 by norm_num, Finset.sum_range_add]
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
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4LeadingSquare_coeff_164 :
    recurrence4LeadingSquare.coeff 164 =
      -(((827605214713464825219866873697743967097915724868492662002340922419 * 10 ^ 70 +
        6592097480285415548893601645100117393217943132237794333578769586145835) * 10 ^ 70 +
        5827346839643299711989434168934988016398276380936740703796002986198819) : ℚ) := by
  unfold recurrence4LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 165,
    remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (164 - x)) = _
  rw [show 165 = 0 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
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
    rw [show 5 = 5 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

private theorem recurrence4LeadingSquare_coeff_165_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (165 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 - x) (by
    omega)]
  norm_num

private theorem recurrence4LeadingSquare_coeff_165_suffix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (165 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4LeadingSquare_coeff_165 :
    recurrence4LeadingSquare.coeff 165 =
      (((761776395750897860001676882701927981774909967221639014797457011014 * 10 ^ 70 +
        8197688070159743007640686975850722281612998495843481784853268571405582) * 10 ^ 70 +
        9200629076069655035045712423752922299161705140176971950981110779325986) : ℚ) := by
  unfold recurrence4LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 166,
    remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (165 - x)) = _
  rw [show 166 = 1 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
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
  rw [recurrence4LeadingSquare_coeff_165_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4LeadingSquare_coeff_165_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4LeadingSquare_coeff_166_prefix_zero :
    (∑ x ∈ Finset.range 2,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (166 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (166 - x) (by
    omega)]
  norm_num

private theorem recurrence4LeadingSquare_coeff_166_suffix_zero :
    (∑ x ∈ Finset.range 2,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (166 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4LeadingSquare_coeff_166 :
    recurrence4LeadingSquare.coeff 166 =
      -(((655001459518548318380337527108124069506388780212302546174053126637 * 10 ^ 70 +
        2033493412034869329046767160396898170359839458220235669237265778928487) * 10 ^ 70 +
        0990724237116850289130006510846164371667270343223991895445106089932607) : ℚ) := by
  unfold recurrence4LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 167,
    remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (166 - x)) = _
  rw [show 167 = 2 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
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
    rw [show 5 = 3 +
      2 by norm_num, Finset.sum_range_add]
  rw [recurrence4LeadingSquare_coeff_166_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4LeadingSquare_coeff_166_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4LeadingSquare_coeff_167_prefix_zero :
    (∑ x ∈ Finset.range 3,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (167 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (167 - x) (by
    omega)]
  norm_num

private theorem recurrence4LeadingSquare_coeff_167_suffix_zero :
    (∑ x ∈ Finset.range 3,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (167 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4LeadingSquare_coeff_167 :
    recurrence4LeadingSquare.coeff 167 =
      (((524224977263957768957460841823558454489630417630360968767528156878 * 10 ^ 70 +
        0057459879090861845110785187139172651213693435546200677823586905261657) * 10 ^ 70 +
        4197850333885647022929090825816669106875160900162014331207827640548218) : ℚ) := by
  unfold recurrence4LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 168,
    remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (167 - x)) = _
  rw [show 168 = 3 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
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
    rw [show 5 = 2 +
      3 by norm_num, Finset.sum_range_add]
  rw [recurrence4LeadingSquare_coeff_167_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4LeadingSquare_coeff_167_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4LeadingSquare_coeff_168_prefix_zero :
    (∑ x ∈ Finset.range 4,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (168 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (168 - x) (by
    omega)]
  norm_num

private theorem recurrence4LeadingSquare_coeff_168_suffix_zero :
    (∑ x ∈ Finset.range 4,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (168 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4LeadingSquare_coeff_168 :
    recurrence4LeadingSquare.coeff 168 =
      -(((385830243214283869097874490813317374360436565447461371267921207637 * 10 ^ 70 +
        4267158747196068785727681183062183804999481806058965226505129669262741) * 10 ^ 70 +
        1992063223744970347339282156152238003521965313560949459664835940583435) : ℚ) := by
  unfold recurrence4LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 169,
    remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (168 - x)) = _
  rw [show 169 = 4 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
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
    rw [show 5 = 1 +
      4 by norm_num, Finset.sum_range_add]
  rw [recurrence4LeadingSquare_coeff_168_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4LeadingSquare_coeff_168_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4LeadingSquare_coeff_169_prefix_zero :
    (∑ x ∈ Finset.range 5,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (169 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (169 - x) (by
    omega)]
  norm_num

private theorem recurrence4LeadingSquare_coeff_169_suffix_zero :
    (∑ x ∈ Finset.range 5,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (169 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4LeadingSquare_coeff_169 :
    recurrence4LeadingSquare.coeff 169 =
      (((253747114393593449536030776044437150893574118724292180234876556467 * 10 ^ 70 +
        7752527768760132640662682663809575446250760174502647867634132191315506) * 10 ^ 70 +
        0627275818872975751136043523459920058646363903898996587371001343372760) : ℚ) := by
  unfold recurrence4LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 170,
    remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (169 - x)) = _
  rw [show 170 = 5 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
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
  rw [recurrence4LeadingSquare_coeff_169_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4LeadingSquare_coeff_169_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4LeadingSquare_coeff_170_prefix_zero :
    (∑ x ∈ Finset.range 6,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (170 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (170 - x) (by
    omega)]
  norm_num

private theorem recurrence4LeadingSquare_coeff_170_suffix_zero :
    (∑ x ∈ Finset.range 6,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (170 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4LeadingSquare_coeff_170 :
    recurrence4LeadingSquare.coeff 170 =
      -(((138235003035896504637634421387034539552754981749327691077872196979 * 10 ^ 70 +
        3162843225189385776035310908316682188518301961431271675181262020307734) * 10 ^ 70 +
        8452741673921032958238765868759081660195691776636215770608770979099137) : ℚ) := by
  unfold recurrence4LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 171,
    remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (170 - x)) = _
  rw [show 171 = 6 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
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
    rw [show 37 = 31 +
      6 by norm_num, Finset.sum_range_add]
  rw [recurrence4LeadingSquare_coeff_170_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4LeadingSquare_coeff_170_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4LeadingSquare_coeff_171_prefix_zero :
    (∑ x ∈ Finset.range 7,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (171 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (171 - x) (by
    omega)]
  norm_num

private theorem recurrence4LeadingSquare_coeff_171_suffix_zero :
    (∑ x ∈ Finset.range 7,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (171 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4LeadingSquare_coeff_171 :
    recurrence4LeadingSquare.coeff 171 =
      (((45414444956533158455779373736567845608226336209056793012278886942 * 10 ^ 70 +
        9632146029959315114680679517444604917678977877426118513304142852704316) * 10 ^ 70 +
        5227861124245574758038502023845617505954395542301272023543523739028134) : ℚ) := by
  unfold recurrence4LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 172,
    remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (171 - x)) = _
  rw [show 172 = 7 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
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
    rw [show 37 = 30 +
      7 by norm_num, Finset.sum_range_add]
  rw [recurrence4LeadingSquare_coeff_171_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4LeadingSquare_coeff_171_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4LeadingSquare_coeff_172_prefix_zero :
    (∑ x ∈ Finset.range 8,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (172 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (172 - x) (by
    omega)]
  norm_num

private theorem recurrence4LeadingSquare_coeff_172_suffix_zero :
    (∑ x ∈ Finset.range 8,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (172 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4LeadingSquare_coeff_172 :
    recurrence4LeadingSquare.coeff 172 =
      (((22525141907092053402660785404837884414702147497527944229781793785 * 10 ^ 70 +
        2781251723554891782971941667065372558159640463091428321097514245344798) * 10 ^ 70 +
        5088502037912418898041588740546418888968234756701526725671330262005091) : ℚ) := by
  unfold recurrence4LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 173,
    remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (172 - x)) = _
  rw [show 173 = 8 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
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
    rw [show 37 = 29 +
      8 by norm_num, Finset.sum_range_add]
  rw [recurrence4LeadingSquare_coeff_172_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4LeadingSquare_coeff_172_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4LeadingSquare_coeff_173_prefix_zero :
    (∑ x ∈ Finset.range 9,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (173 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (173 - x) (by
    omega)]
  norm_num

private theorem recurrence4LeadingSquare_coeff_173_suffix_zero :
    (∑ x ∈ Finset.range 9,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (173 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4LeadingSquare_coeff_173 :
    recurrence4LeadingSquare.coeff 173 =
      -(((66618530425766791120096630457718427015145937217432369863819838718 * 10 ^ 70 +
        0568300084663008477477473782740142429702956664141804932507035729263011) * 10 ^ 70 +
        8287016987060671877834712397837658609497092728773177944333754258094820) : ℚ) := by
  unfold recurrence4LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 174,
    remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (173 - x)) = _
  rw [show 174 = 9 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
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
    rw [show 37 = 28 +
      9 by norm_num, Finset.sum_range_add]
  rw [recurrence4LeadingSquare_coeff_173_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4LeadingSquare_coeff_173_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4LeadingSquare_coeff_174_prefix_zero :
    (∑ x ∈ Finset.range 10,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (174 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (174 - x) (by
    omega)]
  norm_num

private theorem recurrence4LeadingSquare_coeff_174_suffix_zero :
    (∑ x ∈ Finset.range 10,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (174 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4LeadingSquare_coeff_174 :
    recurrence4LeadingSquare.coeff 174 =
      (((90144666026527989555547934906854821629906272996804774247712167623 * 10 ^ 70 +
        7377597772058183663756238623445306127050336719688241354398404899590317) * 10 ^ 70 +
        9416248525240046521788102760107513287662533128250054818554445442139610) : ℚ) := by
  unfold recurrence4LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 175,
    remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (174 - x)) = _
  rw [show 175 = 10 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
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
    rw [show 37 = 27 +
      10 by norm_num, Finset.sum_range_add]
  rw [recurrence4LeadingSquare_coeff_174_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4LeadingSquare_coeff_174_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4LeadingSquare_coeff_175_prefix_zero :
    (∑ x ∈ Finset.range 11,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (175 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (175 - x) (by
    omega)]
  norm_num

private theorem recurrence4LeadingSquare_coeff_175_suffix_zero :
    (∑ x ∈ Finset.range 11,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (175 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4LeadingSquare_coeff_175 :
    recurrence4LeadingSquare.coeff 175 =
      -(((97594312156446209732460989547409350471316446003993429131655522930 * 10 ^ 70 +
        8981142330140553183985689988790996516192936106800456577968528967899750) * 10 ^ 70 +
        3422688766371698016709815840315038351680222914821601431695642674504620) : ℚ) := by
  unfold recurrence4LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 176,
    remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (175 - x)) = _
  rw [show 176 = 11 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
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
    rw [show 37 = 26 +
      11 by norm_num, Finset.sum_range_add]
  rw [recurrence4LeadingSquare_coeff_175_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4LeadingSquare_coeff_175_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4LeadingSquare_coeff_176_prefix_zero :
    (∑ x ∈ Finset.range 12,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (176 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (176 - x) (by
    omega)]
  norm_num

private theorem recurrence4LeadingSquare_coeff_176_suffix_zero :
    (∑ x ∈ Finset.range 12,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (176 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4LeadingSquare_coeff_176 :
    recurrence4LeadingSquare.coeff 176 =
      (((93759782940891402868351736704197845356217844441083034948706090488 * 10 ^ 70 +
        8051900139711289180750271005753135322628529208618899162247437208663651) * 10 ^ 70 +
        8031567490954005926602621140571084329282287679205930833728927155261302) : ℚ) := by
  unfold recurrence4LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 177,
    remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (176 - x)) = _
  rw [show 177 = 12 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
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
    rw [show 37 = 25 +
      12 by norm_num, Finset.sum_range_add]
  rw [recurrence4LeadingSquare_coeff_176_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4LeadingSquare_coeff_176_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4LeadingSquare_coeff_177_prefix_zero :
    (∑ x ∈ Finset.range 13,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (177 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (177 - x) (by
    omega)]
  norm_num

private theorem recurrence4LeadingSquare_coeff_177_suffix_zero :
    (∑ x ∈ Finset.range 13,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (177 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4LeadingSquare_coeff_177 :
    recurrence4LeadingSquare.coeff 177 =
      -(((83053442329299933801673203942571470787989281113116832495944316625 * 10 ^ 70 +
        8334350170688637862291087110891419166067341792611353068167534880874709) * 10 ^ 70 +
        8835811249583853969454141105501540267518695912076035997721606793564330) : ℚ) := by
  unfold recurrence4LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 178,
    remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (177 - x)) = _
  rw [show 178 = 13 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
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
    rw [show 37 = 24 +
      13 by norm_num, Finset.sum_range_add]
  rw [recurrence4LeadingSquare_coeff_177_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4LeadingSquare_coeff_177_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4LeadingSquare_coeff_178_prefix_zero :
    (∑ x ∈ Finset.range 14,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (178 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (178 - x) (by
    omega)]
  norm_num

private theorem recurrence4LeadingSquare_coeff_178_suffix_zero :
    (∑ x ∈ Finset.range 14,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (178 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4LeadingSquare_coeff_178 :
    recurrence4LeadingSquare.coeff 178 =
      (((69092074754004621748465050817926119887220607789414352059075923005 * 10 ^ 70 +
        2368994417668275352121844554854229628161654927558325266482513165496862) * 10 ^ 70 +
        7635385671048378620263788784989540224792898139681290424382888503457227) : ℚ) := by
  unfold recurrence4LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 179,
    remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (178 - x)) = _
  rw [show 179 = 14 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
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
    rw [show 37 = 23 +
      14 by norm_num, Finset.sum_range_add]
  rw [recurrence4LeadingSquare_coeff_178_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4LeadingSquare_coeff_178_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4LeadingSquare_coeff_179_prefix_zero :
    (∑ x ∈ Finset.range 15,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (179 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (179 - x) (by
    omega)]
  norm_num

private theorem recurrence4LeadingSquare_coeff_179_suffix_zero :
    (∑ x ∈ Finset.range 15,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (179 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4LeadingSquare_coeff_179 :
    recurrence4LeadingSquare.coeff 179 =
      -(((54527662505134348048755481403345343475135112273963252246306297071 * 10 ^ 70 +
        5867139428658354816568186691845009164464602107855429120716645338990863) * 10 ^ 70 +
        0841060017061043969902944023637287700582006812569890751776800048224854) : ℚ) := by
  unfold recurrence4LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 180,
    remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (179 - x)) = _
  rw [show 180 = 15 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
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
    rw [show 37 = 22 +
      15 by norm_num, Finset.sum_range_add]
  rw [recurrence4LeadingSquare_coeff_179_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4LeadingSquare_coeff_179_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4LeadingSquare_coeff_180_prefix_zero :
    (∑ x ∈ Finset.range 16,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (180 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (180 - x) (by
    omega)]
  norm_num

private theorem recurrence4LeadingSquare_coeff_180_suffix_zero :
    (∑ x ∈ Finset.range 16,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (180 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4LeadingSquare_coeff_180 :
    recurrence4LeadingSquare.coeff 180 =
      (((41069334904829665223429420691885354147690383822646332439204146434 * 10 ^ 70 +
        1274583547075494602820521096612911775918549939854693055255903553532871) * 10 ^ 70 +
        7974908353985676960792199046252432258208517452186321151587928736623548) : ℚ) := by
  unfold recurrence4LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 181,
    remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (180 - x)) = _
  rw [show 181 = 16 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
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
    rw [show 37 = 21 +
      16 by norm_num, Finset.sum_range_add]
  rw [recurrence4LeadingSquare_coeff_180_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4LeadingSquare_coeff_180_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4LeadingSquare_coeff_181_prefix_zero :
    (∑ x ∈ Finset.range 17,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (181 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (181 - x) (by
    omega)]
  norm_num

private theorem recurrence4LeadingSquare_coeff_181_suffix_zero :
    (∑ x ∈ Finset.range 17,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (181 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4LeadingSquare_coeff_181 :
    recurrence4LeadingSquare.coeff 181 =
      -(((29627179825165827780785859958084825598820914877394685035577634931 * 10 ^ 70 +
        1141340996096814057190369508276311840812290425131973919232863150188079) * 10 ^ 70 +
        0203531675740674464201093523288140401920010244632339135525187422967060) : ℚ) := by
  unfold recurrence4LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 182,
    remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (181 - x)) = _
  rw [show 182 = 17 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
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
    rw [show 37 = 20 +
      17 by norm_num, Finset.sum_range_add]
  rw [recurrence4LeadingSquare_coeff_181_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4LeadingSquare_coeff_181_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4LeadingSquare_coeff_182_prefix_zero :
    (∑ x ∈ Finset.range 18,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (182 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (182 - x) (by
    omega)]
  norm_num

private theorem recurrence4LeadingSquare_coeff_182_suffix_zero :
    (∑ x ∈ Finset.range 18,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (182 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4LeadingSquare_coeff_182 :
    recurrence4LeadingSquare.coeff 182 =
      (((20512082050075401465402704132563630919865096411408404633327304953 * 10 ^ 70 +
        5894315194534747975228346261928155999066676801706866216765034148423815) * 10 ^ 70 +
        2754633670650918571360208115167007003605698661644078046836031472048544) : ℚ) := by
  unfold recurrence4LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 183,
    remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (182 - x)) = _
  rw [show 183 = 18 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
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
    rw [show 37 = 19 +
      18 by norm_num, Finset.sum_range_add]
  rw [recurrence4LeadingSquare_coeff_182_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4LeadingSquare_coeff_182_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4LeadingSquare_coeff_183_prefix_zero :
    (∑ x ∈ Finset.range 19,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (183 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (183 - x) (by
    omega)]
  norm_num

private theorem recurrence4LeadingSquare_coeff_183_suffix_zero :
    (∑ x ∈ Finset.range 19,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (183 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4LeadingSquare_coeff_183 :
    recurrence4LeadingSquare.coeff 183 =
      -(((13640151924655458478605124992121883098498735849394152004177450278 * 10 ^ 70 +
        1108969284404221450689836428488261314845148372916771293560357675034849) * 10 ^ 70 +
        4384541785221592780803345029984723074298410898124611286738801400584026) : ℚ) := by
  unfold recurrence4LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 184,
    remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (183 - x)) = _
  rw [show 184 = 19 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
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
    rw [show 37 = 18 +
      19 by norm_num, Finset.sum_range_add]
  rw [recurrence4LeadingSquare_coeff_183_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4LeadingSquare_coeff_183_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4LeadingSquare_coeff_184_prefix_zero :
    (∑ x ∈ Finset.range 20,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (184 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (184 - x) (by
    omega)]
  norm_num

private theorem recurrence4LeadingSquare_coeff_184_suffix_zero :
    (∑ x ∈ Finset.range 20,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (184 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4LeadingSquare_coeff_184 :
    recurrence4LeadingSquare.coeff 184 =
      (((8708899677694449368390884871933188124987861981658393337181060605 * 10 ^ 70 +
        0671706148296579093767836037980950247935637062337371194964556646093085) * 10 ^ 70 +
        2026697372434093491869433423960042365947375907117122480119527763686449) : ℚ) := by
  unfold recurrence4LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 185,
    remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (184 - x)) = _
  rw [show 185 = 20 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
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
    rw [show 37 = 17 +
      20 by norm_num, Finset.sum_range_add]
  rw [recurrence4LeadingSquare_coeff_184_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4LeadingSquare_coeff_184_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4LeadingSquare_coeff_185_prefix_zero :
    (∑ x ∈ Finset.range 21,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (185 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (185 - x) (by
    omega)]
  norm_num

private theorem recurrence4LeadingSquare_coeff_185_suffix_zero :
    (∑ x ∈ Finset.range 21,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (185 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4LeadingSquare_coeff_185 :
    recurrence4LeadingSquare.coeff 185 =
      -(((5329857611244955750094269894261024700221815681923578375374932014 * 10 ^ 70 +
        2445288203463178085755156069027111210561443759377683743548472495428993) * 10 ^ 70 +
        1946982518501859720299883256776095169405118614131255081120456674979630) : ℚ) := by
  unfold recurrence4LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 186,
    remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (185 - x)) = _
  rw [show 186 = 21 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
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
    rw [show 37 = 16 +
      21 by norm_num, Finset.sum_range_add]
  rw [recurrence4LeadingSquare_coeff_185_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4LeadingSquare_coeff_185_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4LeadingSquare_coeff_186_prefix_zero :
    (∑ x ∈ Finset.range 22,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (186 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (186 - x) (by
    omega)]
  norm_num

private theorem recurrence4LeadingSquare_coeff_186_suffix_zero :
    (∑ x ∈ Finset.range 22,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (186 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4LeadingSquare_coeff_186 :
    recurrence4LeadingSquare.coeff 186 =
      (((3115781803338343378749910981530944617448471166692068149122411109 * 10 ^ 70 +
        5542822601127559208601321230759416156987576400403077751850073233040472) * 10 ^ 70 +
        2672809582429015881171832469266087244673885081700007448448922546660769) : ℚ) := by
  unfold recurrence4LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 187,
    remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (186 - x)) = _
  rw [show 187 = 22 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
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
    rw [show 37 = 15 +
      22 by norm_num, Finset.sum_range_add]
  rw [recurrence4LeadingSquare_coeff_186_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4LeadingSquare_coeff_186_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4LeadingSquare_coeff_187_prefix_zero :
    (∑ x ∈ Finset.range 23,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (187 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (187 - x) (by
    omega)]
  norm_num

private theorem recurrence4LeadingSquare_coeff_187_suffix_zero :
    (∑ x ∈ Finset.range 23,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (187 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4LeadingSquare_coeff_187 :
    recurrence4LeadingSquare.coeff 187 =
      -(((1728864879779653182642533572085641520282383296963250946203179442 * 10 ^ 70 +
        1196052238766766462240552552642168425120683034872981813696319288138777) * 10 ^ 70 +
        6185499813309192304744914537940610880819968339474682645488020591615410) : ℚ) := by
  unfold recurrence4LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 188,
    remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (187 - x)) = _
  rw [show 188 = 23 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
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
    rw [show 37 = 14 +
      23 by norm_num, Finset.sum_range_add]
  rw [recurrence4LeadingSquare_coeff_187_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4LeadingSquare_coeff_187_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4LeadingSquare_coeff_188_prefix_zero :
    (∑ x ∈ Finset.range 24,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (188 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (188 - x) (by
    omega)]
  norm_num

private theorem recurrence4LeadingSquare_coeff_188_suffix_zero :
    (∑ x ∈ Finset.range 24,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (188 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4LeadingSquare_coeff_188 :
    recurrence4LeadingSquare.coeff 188 =
      (((900039877845548416690007908005419183714681244503497258028229643 * 10 ^ 70 +
        1163526285230190291330789993758878015690936697130327572284210549262924) * 10 ^ 70 +
        6721404678688055428925964799154507652240406217152833519762210848584983) : ℚ) := by
  unfold recurrence4LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 189,
    remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (188 - x)) = _
  rw [show 189 = 24 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
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
    rw [show 37 = 13 +
      24 by norm_num, Finset.sum_range_add]
  rw [recurrence4LeadingSquare_coeff_188_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4LeadingSquare_coeff_188_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4LeadingSquare_coeff_189_prefix_zero :
    (∑ x ∈ Finset.range 25,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (189 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (189 - x) (by
    omega)]
  norm_num

private theorem recurrence4LeadingSquare_coeff_189_suffix_zero :
    (∑ x ∈ Finset.range 25,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (189 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4LeadingSquare_coeff_189 :
    recurrence4LeadingSquare.coeff 189 =
      -(((429712233199633839991567293363439365139532470445696674062340781 * 10 ^ 70 +
        1266080421415402396014443132396550435974585103110738532959311604829995) * 10 ^ 70 +
        5488963517010354888201163563854527455213849092513384386559782951416072) : ℚ) := by
  unfold recurrence4LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 190,
    remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (189 - x)) = _
  rw [show 190 = 25 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
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
    rw [show 37 = 12 +
      25 by norm_num, Finset.sum_range_add]
  rw [recurrence4LeadingSquare_coeff_189_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4LeadingSquare_coeff_189_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
