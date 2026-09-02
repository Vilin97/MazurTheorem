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

private theorem recurrence4A4Square_coeff_222_prefix_zero :
    (∑ x ∈ Finset.range 44,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (222 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (222 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_222_suffix_zero :
    (∑ x ∈ Finset.range 44,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (222 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_222 :
    recurrence4A4Square.coeff 222 =
      (((1182072006687935465273941831606394974808607223739731 * 10 ^ 70 +
        6315552030352667797067171269214974984286911680281254850565786724981345) * 10 ^ 70 +
        0281232893484383628358475326456128867352810113039991328703961788380016) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 223,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (222 - x)) = _
  rw [show 223 = 44 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 7 +
      44 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_222_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_222_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_223_prefix_zero :
    (∑ x ∈ Finset.range 45,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (223 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (223 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_223_suffix_zero :
    (∑ x ∈ Finset.range 45,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (223 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_223 :
    recurrence4A4Square.coeff 223 =
      -(((587387178885558399965447221522601124297839214080941 * 10 ^ 70 +
        1347968242824723279138538497288698516495064153226996167043948391607072) * 10 ^ 70 +
        8681459426811015069191051951419074011383585885151862310623956332715322) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 224,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (223 - x)) = _
  rw [show 224 = 45 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 6 +
      45 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_223_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_223_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_224_prefix_zero :
    (∑ x ∈ Finset.range 46,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (224 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (224 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_224_suffix_zero :
    (∑ x ∈ Finset.range 46,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (224 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_224 :
    recurrence4A4Square.coeff 224 =
      (((286295299152058462086833904026207012627376354149729 * 10 ^ 70 +
        6857826224996465823614014020804227595347206566651258642192142733167126) * 10 ^ 70 +
        2758626364785829528547888737304577479639227952576160355387941559789989) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 225,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (224 - x)) = _
  rw [show 225 = 46 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 5 +
      46 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_224_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_224_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_225_prefix_zero :
    (∑ x ∈ Finset.range 47,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (225 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (225 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_225_suffix_zero :
    (∑ x ∈ Finset.range 47,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (225 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_225 :
    recurrence4A4Square.coeff 225 =
      -(((136865015299054938140534792459627288506058948285054 * 10 ^ 70 +
        4294997364099332501541645378962925576719285251592204849839987029957172) * 10 ^ 70 +
        9390851864849431178149512409250361582500685954921573713311943394948086) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 226,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (225 - x)) = _
  rw [show 226 = 47 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 4 +
      47 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_225_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_225_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_226_prefix_zero :
    (∑ x ∈ Finset.range 48,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (226 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (226 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_226_suffix_zero :
    (∑ x ∈ Finset.range 48,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (226 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_226 :
    recurrence4A4Square.coeff 226 =
      (((64170934622251829717605530121159757866281281710084 * 10 ^ 70 +
        4833189201077549808735850632565546437225617081772128005400818131125379) * 10 ^ 70 +
        5415261745342372382960152330503058896686600323588515281189409125536025) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 227,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (226 - x)) = _
  rw [show 227 = 48 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 3 +
      48 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_226_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_226_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_227_prefix_zero :
    (∑ x ∈ Finset.range 49,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (227 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (227 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_227_suffix_zero :
    (∑ x ∈ Finset.range 49,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (227 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_227 :
    recurrence4A4Square.coeff 227 =
      -(((29507292774058430489856995898889332098228077405321 * 10 ^ 70 +
        4059870618158936542519553811707327881534606341428212621359012222647246) * 10 ^ 70 +
        6477885878814018626197833334104619592245268432188161223588775033771966) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 228,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (227 - x)) = _
  rw [show 228 = 49 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 2 +
      49 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_227_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_227_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_228_prefix_zero :
    (∑ x ∈ Finset.range 50,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (228 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (228 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_228_suffix_zero :
    (∑ x ∈ Finset.range 50,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (228 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_228 :
    recurrence4A4Square.coeff 228 =
      (((13305705396080431929332769657755651930643357127411 * 10 ^ 70 +
        7195797961797084156292218224126032861824257596762122244961492406834019) * 10 ^ 70 +
        9982670702463847841885452658763462193221039799023873642671770289372383) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 229,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (228 - x)) = _
  rw [show 229 = 50 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 1 +
      50 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_228_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_228_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_229_prefix_zero :
    (∑ x ∈ Finset.range 51,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (229 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (229 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_229_suffix_zero :
    (∑ x ∈ Finset.range 51,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (229 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_229 :
    recurrence4A4Square.coeff 229 =
      -(((5883368513232270154410150391060792563042276943545 * 10 ^ 70 +
        7105090254961782204815255730662422728633950181291567541723001243928726) * 10 ^ 70 +
        4322758309480132793433623676315308420152725622704849945234842118656258) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 230,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (229 - x)) = _
  rw [show 230 = 51 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_229_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_229_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_230_prefix_zero :
    (∑ x ∈ Finset.range 52,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (230 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (230 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_230_suffix_zero :
    (∑ x ∈ Finset.range 52,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (230 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_230 :
    recurrence4A4Square.coeff 230 =
      (((2550565669300601948233770722524602336400276486864 * 10 ^ 70 +
        1070356695309750931057907913194849040296785415908485681511384610110583) * 10 ^ 70 +
        9950711738336692454579166698660832038423509325594143254846800926649234) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 231,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (230 - x)) = _
  rw [show 231 = 52 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 31 +
      52 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_230_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_230_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_231_prefix_zero :
    (∑ x ∈ Finset.range 53,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (231 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (231 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_231_suffix_zero :
    (∑ x ∈ Finset.range 53,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (231 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_231 :
    recurrence4A4Square.coeff 231 =
      -(((1083871866237738013157854448994005078112920603169 * 10 ^ 70 +
        8705963627531216393441476884008499808328391376940376472136039642116379) * 10 ^ 70 +
        0664023131428780213925032826362663377833147257764592897482832314878428) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 232,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (231 - x)) = _
  rw [show 232 = 53 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 30 +
      53 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_231_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_231_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_232_prefix_zero :
    (∑ x ∈ Finset.range 54,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (232 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (232 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_232_suffix_zero :
    (∑ x ∈ Finset.range 54,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (232 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_232 :
    recurrence4A4Square.coeff 232 =
      (((451337461231392083823400454395843936358491391833 * 10 ^ 70 +
        2141683281152033298712764279971574078837861494422517244763529872654959) * 10 ^ 70 +
        9278023093493557581988599099856781346780342958110690217636814341652101) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 233,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (232 - x)) = _
  rw [show 233 = 54 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 29 +
      54 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_232_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_232_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_233_prefix_zero :
    (∑ x ∈ Finset.range 55,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (233 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (233 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_233_suffix_zero :
    (∑ x ∈ Finset.range 55,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (233 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_233 :
    recurrence4A4Square.coeff 233 =
      -(((184061228749705608867962422276217477581418740921 * 10 ^ 70 +
        4257203592128523800744211633611130076858570692414317121780565203037616) * 10 ^ 70 +
        9978278203184455940743122409012141881422890992755873086194368422168524) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 234,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (233 - x)) = _
  rw [show 234 = 55 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 28 +
      55 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_233_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_233_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_234_prefix_zero :
    (∑ x ∈ Finset.range 56,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (234 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (234 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_234_suffix_zero :
    (∑ x ∈ Finset.range 56,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (234 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_234 :
    recurrence4A4Square.coeff 234 =
      (((73444548346850233120491989880831688816375800517 * 10 ^ 70 +
        1791221534317479306169580639691453360434012707794829989545738065991717) * 10 ^ 70 +
        7961429829588335880564315454527127983366942109245065744828781191468890) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 235,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (234 - x)) = _
  rw [show 235 = 56 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 27 +
      56 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_234_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_234_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_235_prefix_zero :
    (∑ x ∈ Finset.range 57,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (235 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (235 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_235_suffix_zero :
    (∑ x ∈ Finset.range 57,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (235 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_235 :
    recurrence4A4Square.coeff 235 =
      -(((28630906563385700223159189064581799897391020033 * 10 ^ 70 +
        3022848824710971145856082364218516096948204349960921741574086285396309) * 10 ^ 70 +
        5274942297012813494073232648688462672997682060288939120211456633508130) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 236,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (235 - x)) = _
  rw [show 236 = 57 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 26 +
      57 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_235_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_235_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_236_prefix_zero :
    (∑ x ∈ Finset.range 58,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (236 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (236 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_236_suffix_zero :
    (∑ x ∈ Finset.range 58,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (236 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_236 :
    recurrence4A4Square.coeff 236 =
      (((10876899490807753165004497550026090969712134504 * 10 ^ 70 +
        4435951584059901798635623988135120131974877633375727756068752014430206) * 10 ^ 70 +
        4662352164577120573833789204906880633943935830113479199416380059429090) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 237,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (236 - x)) = _
  rw [show 237 = 58 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 25 +
      58 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_236_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_236_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_237_prefix_zero :
    (∑ x ∈ Finset.range 59,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (237 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (237 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_237_suffix_zero :
    (∑ x ∈ Finset.range 59,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (237 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_237 :
    recurrence4A4Square.coeff 237 =
      -(((4010153182041902387397965679786576913084632243 * 10 ^ 70 +
        5081092307890882590374112469758317014320929153310555342679030287487639) * 10 ^ 70 +
        4084729175166013867804327113152553506079683852455029491177792196378374) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 238,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (237 - x)) = _
  rw [show 238 = 59 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 24 +
      59 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_237_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_237_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_238_prefix_zero :
    (∑ x ∈ Finset.range 60,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (238 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (238 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_238_suffix_zero :
    (∑ x ∈ Finset.range 60,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (238 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_238 :
    recurrence4A4Square.coeff 238 =
      (((1424619862770770602974181334294980994819813541 * 10 ^ 70 +
        0654426776882495169377318529067988116872939455910444645598659930864839) * 10 ^ 70 +
        6370914687686280347490402249338129806097147366220324609456638973942054) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 239,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (238 - x)) = _
  rw [show 239 = 60 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 23 +
      60 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_238_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_238_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_239_prefix_zero :
    (∑ x ∈ Finset.range 61,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (239 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (239 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_239_suffix_zero :
    (∑ x ∈ Finset.range 61,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (239 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_239 :
    recurrence4A4Square.coeff 239 =
      -(((481402160605715353824800282597551798710386104 * 10 ^ 70 +
        0350943089520132276304672285341340716314902706457828140911507345617207) * 10 ^ 70 +
        2968094493114622899718077557218247533673066230168452958679073513114944) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 240,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (239 - x)) = _
  rw [show 240 = 61 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 22 +
      61 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_239_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_239_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_240_prefix_zero :
    (∑ x ∈ Finset.range 62,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (240 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (240 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_240_suffix_zero :
    (∑ x ∈ Finset.range 62,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (240 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_240 :
    recurrence4A4Square.coeff 240 =
      (((150814003708600334689468173676746520219541343 * 10 ^ 70 +
        4293997418577022447689132261479272595891706525285968693814754345878656) * 10 ^ 70 +
        0628739684226077446589249716335316945441056410992870429334406079012263) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 241,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (240 - x)) = _
  rw [show 241 = 62 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 21 +
      62 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_240_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_240_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_241_prefix_zero :
    (∑ x ∈ Finset.range 63,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (241 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (241 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_241_suffix_zero :
    (∑ x ∈ Finset.range 63,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (241 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_241 :
    recurrence4A4Square.coeff 241 =
      -(((41219337098227641049188619063138316858461342 * 10 ^ 70 +
        2873463372340363260191972436744171753174459681295383645897871652809789) * 10 ^ 70 +
        9785026992650745719620565020744671211283616492118834108911686276386736) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 242,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (241 - x)) = _
  rw [show 242 = 63 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 20 +
      63 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_241_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_241_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_242_prefix_zero :
    (∑ x ∈ Finset.range 64,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (242 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (242 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_242_suffix_zero :
    (∑ x ∈ Finset.range 64,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (242 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_242 :
    recurrence4A4Square.coeff 242 =
      (((7951633227299256341857780811570982302603058 * 10 ^ 70 +
        0952781203074019560090342782741653076777664759530341349796080250145951) * 10 ^ 70 +
        2998502525121153070018747662403805179816678903034978525306975232170446) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 243,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (242 - x)) = _
  rw [show 243 = 64 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 19 +
      64 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_242_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_242_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_243_prefix_zero :
    (∑ x ∈ Finset.range 65,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (243 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (243 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_243_suffix_zero :
    (∑ x ∈ Finset.range 65,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (243 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_243 :
    recurrence4A4Square.coeff 243 =
      (((553508804672517185250606757512073270506886 * 10 ^ 70 +
        6151817816308393581580756094585966108799911606578864483279408469835849) * 10 ^ 70 +
        9053749981807150107216707297520476488791723773541771968702874259553414) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 244,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (243 - x)) = _
  rw [show 244 = 65 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 18 +
      65 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_243_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_243_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_244_prefix_zero :
    (∑ x ∈ Finset.range 66,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (244 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (244 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_244_suffix_zero :
    (∑ x ∈ Finset.range 66,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (244 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_244 :
    recurrence4A4Square.coeff 244 =
      -(((1821349884975631401632426465622100827982703 * 10 ^ 70 +
        1038167438777899590268615308561107094962171870187763886743796799142693) * 10 ^ 70 +
        5722702708078112268012737733312279084805736782768531924057337651849149) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 245,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (244 - x)) = _
  rw [show 245 = 66 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 17 +
      66 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_244_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_244_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_245_prefix_zero :
    (∑ x ∈ Finset.range 67,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (245 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (245 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_245_suffix_zero :
    (∑ x ∈ Finset.range 67,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (245 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_245 :
    recurrence4A4Square.coeff 245 =
      (((1398688422480095937643768166122495297517583 * 10 ^ 70 +
        9017369386907710775289253828641318371122615967720659516254732925160782) * 10 ^ 70 +
        6040860914553697699409692539193634725445516497802456767151212785850176) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 246,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (245 - x)) = _
  rw [show 246 = 67 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 16 +
      67 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_245_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_245_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_246_prefix_zero :
    (∑ x ∈ Finset.range 68,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (246 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (246 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_246_suffix_zero :
    (∑ x ∈ Finset.range 68,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (246 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_246 :
    recurrence4A4Square.coeff 246 =
      -(((832833975761331623783840198805311029814235 * 10 ^ 70 +
        6375829542184076299768026838236881555342966344107517488564878016315949) * 10 ^ 70 +
        8118662987170325191984906583289625939841728950003841232009103268020833) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 247,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (246 - x)) = _
  rw [show 247 = 68 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 15 +
      68 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_246_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_246_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_247_prefix_zero :
    (∑ x ∈ Finset.range 69,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (247 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (247 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_247_suffix_zero :
    (∑ x ∈ Finset.range 69,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (247 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_247 :
    recurrence4A4Square.coeff 247 =
      (((441100780104237099283582472077819318383077 * 10 ^ 70 +
        2988607998125540006588679792428858966171960353490791569503430207054510) * 10 ^ 70 +
        2799487062478804313764611695385400150768442867521792836414897338901754) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 248,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (247 - x)) = _
  rw [show 248 = 69 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 14 +
      69 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_247_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_247_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_248_prefix_zero :
    (∑ x ∈ Finset.range 70,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (248 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (248 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_248_suffix_zero :
    (∑ x ∈ Finset.range 70,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (248 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_248 :
    recurrence4A4Square.coeff 248 =
      -(((217392405413474742886769779826160848499171 * 10 ^ 70 +
        3099986634023406094584206085519661082963845423600406597059885301605048) * 10 ^ 70 +
        8239461339888052365938073027841878261142878344096508367349881380638915) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 249,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (248 - x)) = _
  rw [show 249 = 70 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 13 +
      70 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_248_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_248_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_249_prefix_zero :
    (∑ x ∈ Finset.range 71,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (249 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (249 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_249_suffix_zero :
    (∑ x ∈ Finset.range 71,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (249 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_249 :
    recurrence4A4Square.coeff 249 =
      (((101692422626176305229235542347769455180085 * 10 ^ 70 +
        3487794440308386651932750058024339843590181277050997865446545913063388) * 10 ^ 70 +
        8845675170733729662355417896997005409088448097083973087942841638329692) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 250,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (249 - x)) = _
  rw [show 250 = 71 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 12 +
      71 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_249_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_249_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_250_prefix_zero :
    (∑ x ∈ Finset.range 72,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (250 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (250 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_250_suffix_zero :
    (∑ x ∈ Finset.range 72,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (250 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_250 :
    recurrence4A4Square.coeff 250 =
      -(((45605644560845772425388147654709390905260 * 10 ^ 70 +
        7129968352668274466756284497147189298931405102680819472442327970630743) * 10 ^ 70 +
        8423250234102116514365160196387327661534815125520500208058457618199205) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 251,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (250 - x)) = _
  rw [show 251 = 72 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 11 +
      72 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_250_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_250_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_251_prefix_zero :
    (∑ x ∈ Finset.range 73,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (251 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (251 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_251_suffix_zero :
    (∑ x ∈ Finset.range 73,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (251 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_251 :
    recurrence4A4Square.coeff 251 =
      (((19714480869006677001150494087463191100912 * 10 ^ 70 +
        4674170101209207959603220286632181228208818471679157379121442344106936) * 10 ^ 70 +
        5992073161892982077171335216863383982961641260851867430210212625697582) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 252,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (251 - x)) = _
  rw [show 252 = 73 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 10 +
      73 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_251_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_251_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_252_prefix_zero :
    (∑ x ∈ Finset.range 74,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (252 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (252 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_252_suffix_zero :
    (∑ x ∈ Finset.range 74,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (252 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_252 :
    recurrence4A4Square.coeff 252 =
      -(((8239185022821842923548259068891136683096 * 10 ^ 70 +
        7837123382474581649436479865432571490646066701271086849087883464594223) * 10 ^ 70 +
        3826746141195144365356384949438178041421629575408343337793299624941245) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 253,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (252 - x)) = _
  rw [show 253 = 74 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 9 +
      74 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_252_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_252_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
