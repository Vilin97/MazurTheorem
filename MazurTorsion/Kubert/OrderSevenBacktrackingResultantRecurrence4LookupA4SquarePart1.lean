/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupA4
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: A4Square coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_253_prefix_zero :
    (∑ x ∈ Finset.range 75,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (253 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (253 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_253_suffix_zero :
    (∑ x ∈ Finset.range 75,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (253 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_253 :
    recurrence4A4Square.coeff 253 =
      (((3334250186570544621330134459424936062695 * 10 ^ 70 +
        1365642914120568709955954841996561192315049940443501524744020493620935) * 10 ^ 70 +
        8892171425198616415680499600498661504149052057252028366445587770925068) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 254,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (253 - x)) = _
  rw [show 254 = 75 +
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
    rw [show 83 = 8 +
      75 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_253_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_253_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_254_prefix_zero :
    (∑ x ∈ Finset.range 76,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (254 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (254 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_254_suffix_zero :
    (∑ x ∈ Finset.range 76,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (254 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_254 :
    recurrence4A4Square.coeff 254 =
      -(((1307424369779126776600925686421881005534 * 10 ^ 70 +
        7231538897068108938789322819870093568795802602749443026836035311645980) * 10 ^ 70 +
        7946700394089438610074641759910412507733010966040620289015975441742460) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 255,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (254 - x)) = _
  rw [show 255 = 76 +
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
    rw [show 83 = 7 +
      76 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_254_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_254_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_255_prefix_zero :
    (∑ x ∈ Finset.range 77,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (255 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (255 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_255_suffix_zero :
    (∑ x ∈ Finset.range 77,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (255 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_255 :
    recurrence4A4Square.coeff 255 =
      (((496745582674089117666607219370469191337 * 10 ^ 70 +
        1597278715026185124692445737934678945561106670498926000664243364059104) * 10 ^ 70 +
        2706488513373146760588449396167535757164785986487327294514573279405050) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 256,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (255 - x)) = _
  rw [show 256 = 77 +
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
    rw [show 83 = 6 +
      77 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_255_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_255_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_256_prefix_zero :
    (∑ x ∈ Finset.range 78,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (256 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (256 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_256_suffix_zero :
    (∑ x ∈ Finset.range 78,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (256 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_256 :
    recurrence4A4Square.coeff 256 =
      -(((182752558064251318911874502804192682097 * 10 ^ 70 +
        3736834581292419291420656036119288618057711710514643386020138037414463) * 10 ^ 70 +
        9437015380529109675981557326154620576425926650292556885776285435952631) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 257,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (256 - x)) = _
  rw [show 257 = 78 +
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
    rw [show 83 = 5 +
      78 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_256_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_256_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_257_prefix_zero :
    (∑ x ∈ Finset.range 79,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (257 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (257 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_257_suffix_zero :
    (∑ x ∈ Finset.range 79,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (257 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_257 :
    recurrence4A4Square.coeff 257 =
      (((65007007383412086367735723936935476798 * 10 ^ 70 +
        9662611089418312747624184879602734725596686569083046628504878581217805) * 10 ^ 70 +
        8698238459337009132349756374880349679568335087621790200655851857207338) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 258,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (257 - x)) = _
  rw [show 258 = 79 +
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
    rw [show 83 = 4 +
      79 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_257_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_257_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_258_prefix_zero :
    (∑ x ∈ Finset.range 80,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (258 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (258 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_258_suffix_zero :
    (∑ x ∈ Finset.range 80,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (258 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_258 :
    recurrence4A4Square.coeff 258 =
      -(((22295104583538099814363591962019919249 * 10 ^ 70 +
        1424863237821284784619420427366634535942303070462772977253966768265856) * 10 ^ 70 +
        7559759012614211865089947630288293425897526169911443444847983220682226) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 259,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (258 - x)) = _
  rw [show 259 = 80 +
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
    rw [show 83 = 3 +
      80 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_258_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_258_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_259_prefix_zero :
    (∑ x ∈ Finset.range 81,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (259 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (259 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_259_suffix_zero :
    (∑ x ∈ Finset.range 81,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (259 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_259 :
    recurrence4A4Square.coeff 259 =
      (((7334171452723174731146014079360866816 * 10 ^ 70 +
        0125978382959504597067814839512187395915514793498863362664943324220143) * 10 ^ 70 +
        7577909518695966032947171713225010795242616041436098072408584079576142) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 260,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (259 - x)) = _
  rw [show 260 = 81 +
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
    rw [show 83 = 2 +
      81 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_259_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_259_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_260_prefix_zero :
    (∑ x ∈ Finset.range 82,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (260 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (260 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_260_suffix_zero :
    (∑ x ∈ Finset.range 82,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (260 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_260 :
    recurrence4A4Square.coeff 260 =
      -(((2290867580753899267215172520636134469 * 10 ^ 70 +
        2907822296986258418593987471610610123708437362523472196327337629908544) * 10 ^ 70 +
        4402912408821580925960515963234514536977366939002110623249009866552144) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 261,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (260 - x)) = _
  rw [show 261 = 82 +
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
    rw [show 83 = 1 +
      82 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_260_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_260_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_261_prefix_zero :
    (∑ x ∈ Finset.range 83,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (261 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (261 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_261_suffix_zero :
    (∑ x ∈ Finset.range 83,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (261 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_261 :
    recurrence4A4Square.coeff 261 =
      (((665166819272931587410741094221310527 * 10 ^ 70 +
        7416063421358579756330377165313893199511596426883041110286292243344772) * 10 ^ 70 +
        9582145180662193573835905177002351298983836120114375825878016192420266) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 262,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (261 - x)) = _
  rw [show 262 = 83 +
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
  rw [recurrence4A4Square_coeff_261_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_261_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_262_prefix_zero :
    (∑ x ∈ Finset.range 84,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (262 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (262 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_262_suffix_zero :
    (∑ x ∈ Finset.range 84,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (262 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_262 :
    recurrence4A4Square.coeff 262 =
      -(((170458667554407295520505928129163860 * 10 ^ 70 +
        2429359770272207102889305070155813801150307332339984176006931379440410) * 10 ^ 70 +
        4923849576166556023455161694652168512836105405508591308468297119384279) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 263,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (262 - x)) = _
  rw [show 263 = 84 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 31 +
      84 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_262_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_262_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_263_prefix_zero :
    (∑ x ∈ Finset.range 85,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (263 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (263 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_263_suffix_zero :
    (∑ x ∈ Finset.range 85,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (263 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_263 :
    recurrence4A4Square.coeff 263 =
      (((32343209955751840269224398128175565 * 10 ^ 70 +
        3966156552588713625613624366046719366396048088429609357518211258295674) * 10 ^ 70 +
        4834350559079847170820194723995366926495289409235890677299496251423624) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 264,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (263 - x)) = _
  rw [show 264 = 85 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 30 +
      85 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_263_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_263_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_264_prefix_zero :
    (∑ x ∈ Finset.range 86,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (264 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (264 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_264_suffix_zero :
    (∑ x ∈ Finset.range 86,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (264 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_264 :
    recurrence4A4Square.coeff 264 =
      (((424327842247054629122606528344247 * 10 ^ 70 +
        2956897354526727039556405152279339230471395581528785080030128168415656) * 10 ^ 70 +
        4603883038758783870797677745465982314531198607413327501891848558267855) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 265,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (264 - x)) = _
  rw [show 265 = 86 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 29 +
      86 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_264_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_264_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_265_prefix_zero :
    (∑ x ∈ Finset.range 87,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (265 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (265 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_265_suffix_zero :
    (∑ x ∈ Finset.range 87,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (265 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_265 :
    recurrence4A4Square.coeff 265 =
      -(((5156434765122720605117203530084609 * 10 ^ 70 +
        9643610314087882190183697372014130333169830756230998937318509477667722) * 10 ^ 70 +
        9924427374790941143511516943066459586506160311723128033726534388002810) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 266,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (265 - x)) = _
  rw [show 266 = 87 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 28 +
      87 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_265_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_265_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_266_prefix_zero :
    (∑ x ∈ Finset.range 88,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (266 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (266 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_266_suffix_zero :
    (∑ x ∈ Finset.range 88,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (266 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_266 :
    recurrence4A4Square.coeff 266 =
      (((3926986961067766470550426793556010 * 10 ^ 70 +
        1161486613839964308525806215300343327325115192936365835096623729060572) * 10 ^ 70 +
        3181105558000728180463220863705797508079537334430031107640641498664827) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 267,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (266 - x)) = _
  rw [show 267 = 88 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 27 +
      88 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_266_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_266_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_267_prefix_zero :
    (∑ x ∈ Finset.range 89,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (267 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (267 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_267_suffix_zero :
    (∑ x ∈ Finset.range 89,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (267 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_267 :
    recurrence4A4Square.coeff 267 =
      -(((2264053692000016079092199177864114 * 10 ^ 70 +
        0174017694976982485987867841279579014824618437698688444732924851669480) * 10 ^ 70 +
        5562147895332512023097829110429083162000191887708794145607685505776382) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 268,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (267 - x)) = _
  rw [show 268 = 89 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 26 +
      89 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_267_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_267_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_268_prefix_zero :
    (∑ x ∈ Finset.range 90,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (268 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (268 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_268_suffix_zero :
    (∑ x ∈ Finset.range 90,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (268 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_268 :
    recurrence4A4Square.coeff 268 =
      (((1157890624054774037667119761868875 * 10 ^ 70 +
        0040844520168753960779614130053879855228073488239902382769447446607660) * 10 ^ 70 +
        6076937046684130295197276011184184818398157550164320931957182239709672) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 269,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (268 - x)) = _
  rw [show 269 = 90 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 25 +
      90 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_268_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_268_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_269_prefix_zero :
    (∑ x ∈ Finset.range 91,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (269 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (269 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_269_suffix_zero :
    (∑ x ∈ Finset.range 91,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (269 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_269 :
    recurrence4A4Square.coeff 269 =
      -(((550644677130346430402569767001389 * 10 ^ 70 +
        8502545217100047341644197395825296025436406237639648255749199853730173) * 10 ^ 70 +
        7295849693696514149744371264515360903570104213859558347638119584665176) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 270,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (269 - x)) = _
  rw [show 270 = 91 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 24 +
      91 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_269_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_269_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_270_prefix_zero :
    (∑ x ∈ Finset.range 92,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (270 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (270 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_270_suffix_zero :
    (∑ x ∈ Finset.range 92,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (270 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_270 :
    recurrence4A4Square.coeff 270 =
      (((247918440393908032496062288544353 * 10 ^ 70 +
        8881994330801484194631800991244827224183764096163661928720190902118182) * 10 ^ 70 +
        9358556686925026661867085373413011873079548592098672873367494150545646) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 271,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (270 - x)) = _
  rw [show 271 = 92 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 23 +
      92 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_270_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_270_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_271_prefix_zero :
    (∑ x ∈ Finset.range 93,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (271 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (271 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_271_suffix_zero :
    (∑ x ∈ Finset.range 93,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (271 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_271 :
    recurrence4A4Square.coeff 271 =
      -(((106398701128939315039237782857771 * 10 ^ 70 +
        7374200466788896383918442549871848837313270040455460086933490785175778) * 10 ^ 70 +
        9735079223596904357419695470048254168236551580166689271090446987987374) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 272,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (271 - x)) = _
  rw [show 272 = 93 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 22 +
      93 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_271_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_271_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_272_prefix_zero :
    (∑ x ∈ Finset.range 94,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (272 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (272 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_272_suffix_zero :
    (∑ x ∈ Finset.range 94,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (272 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_272 :
    recurrence4A4Square.coeff 272 =
      (((43592530608905618360187516329307 * 10 ^ 70 +
        2408147547096942175392759613382114161261831695877230597323258031885604) * 10 ^ 70 +
        2876180190651664937321385319233217514308892555160121125500218671081093) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 273,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (272 - x)) = _
  rw [show 273 = 94 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 21 +
      94 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_272_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_272_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_273_prefix_zero :
    (∑ x ∈ Finset.range 95,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (273 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (273 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_273_suffix_zero :
    (∑ x ∈ Finset.range 95,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (273 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_273 :
    recurrence4A4Square.coeff 273 =
      -(((17024560882164365378638021536230 * 10 ^ 70 +
        3456696192245086027856059826688109515349839787091359051054544693638230) * 10 ^ 70 +
        6179918376392574918768571816775847534020763465665751763481004279073376) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 274,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (273 - x)) = _
  rw [show 274 = 95 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 20 +
      95 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_273_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_273_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_274_prefix_zero :
    (∑ x ∈ Finset.range 96,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (274 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (274 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_274_suffix_zero :
    (∑ x ∈ Finset.range 96,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (274 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_274 :
    recurrence4A4Square.coeff 274 =
      (((6313595267652041714267414899162 * 10 ^ 70 +
        0241993690662354807561082546704081874107523464595282902304389821482125) * 10 ^ 70 +
        8350079805890920095943951191992427827565827650643567583734803376430814) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 275,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (274 - x)) = _
  rw [show 275 = 96 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 19 +
      96 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_274_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_274_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_275_prefix_zero :
    (∑ x ∈ Finset.range 97,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (275 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (275 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_275_suffix_zero :
    (∑ x ∈ Finset.range 97,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (275 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_275 :
    recurrence4A4Square.coeff 275 =
      -(((2209544450645312787362870846500 * 10 ^ 70 +
        5708189127529489478849469959835526005970831265466301706189464295625863) * 10 ^ 70 +
        0069652939985572293704122443571372554836564664277109233951834147419492) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 276,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (275 - x)) = _
  rw [show 276 = 97 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 18 +
      97 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_275_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_275_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_276_prefix_zero :
    (∑ x ∈ Finset.range 98,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (276 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (276 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_276_suffix_zero :
    (∑ x ∈ Finset.range 98,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (276 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_276 :
    recurrence4A4Square.coeff 276 =
      (((722577472554235050082938608506 * 10 ^ 70 +
        3775887527901364549921129380987940726424170237982345273130430874196577) * 10 ^ 70 +
        3373891627297531773483570474773421130822307338946494187339008414239055) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 277,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (276 - x)) = _
  rw [show 277 = 98 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 17 +
      98 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_276_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_276_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_277_prefix_zero :
    (∑ x ∈ Finset.range 99,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (277 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (277 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_277_suffix_zero :
    (∑ x ∈ Finset.range 99,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (277 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_277 :
    recurrence4A4Square.coeff 277 =
      -(((217215955554990834236777202409 * 10 ^ 70 +
        2646356862113469060279649431721257025113227571147558399698569884379493) * 10 ^ 70 +
        4767660983995530661790002899737793609578418268793299419312033337232332) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 278,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (277 - x)) = _
  rw [show 278 = 99 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 16 +
      99 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_277_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_277_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_278_prefix_zero :
    (∑ x ∈ Finset.range 100,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (278 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (278 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_278_suffix_zero :
    (∑ x ∈ Finset.range 100,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (278 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_278 :
    recurrence4A4Square.coeff 278 =
      (((58186368348956106168888862718 * 10 ^ 70 +
        9191682092688179667452230630317489875765623863933950907402351999092447) * 10 ^ 70 +
        8393267785659121438264355260460151666374330561393560272747595026944948) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 279,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (278 - x)) = _
  rw [show 279 = 100 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 15 +
      100 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_278_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_278_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_279_prefix_zero :
    (∑ x ∈ Finset.range 101,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (279 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (279 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_279_suffix_zero :
    (∑ x ∈ Finset.range 101,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (279 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_279 :
    recurrence4A4Square.coeff 279 =
      -(((12905931283503570123803351408 * 10 ^ 70 +
        9675115328719241106117701239065243853307322559995838989447548090054355) * 10 ^ 70 +
        6654199794177137893054266716335010079749968438496122826185023396361562) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 280,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (279 - x)) = _
  rw [show 280 = 101 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 14 +
      101 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_279_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_279_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_280_prefix_zero :
    (∑ x ∈ Finset.range 102,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (280 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (280 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_280_suffix_zero :
    (∑ x ∈ Finset.range 102,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (280 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_280 :
    recurrence4A4Square.coeff 280 =
      (((1794557209716433293654742641 * 10 ^ 70 +
        4969638033672432542154865183536163352113706601556875623619304218813293) * 10 ^ 70 +
        3777809508752058976464882131064898402801653804979942920627630352224759) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 281,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (280 - x)) = _
  rw [show 281 = 102 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 13 +
      102 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_280_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_280_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_281_prefix_zero :
    (∑ x ∈ Finset.range 103,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (281 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (281 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_281_suffix_zero :
    (∑ x ∈ Finset.range 103,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (281 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_281 :
    recurrence4A4Square.coeff 281 =
      (((244785599943422337929280395 * 10 ^ 70 +
        6781484951184627586482320229335687926170149681698346614706191595003797) * 10 ^ 70 +
        2037731931613561594563042561568510032898283860650635105648011826071954) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 282,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (281 - x)) = _
  rw [show 282 = 103 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 12 +
      103 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_281_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_281_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_282_prefix_zero :
    (∑ x ∈ Finset.range 104,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (282 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (282 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_282_suffix_zero :
    (∑ x ∈ Finset.range 104,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (282 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_282 :
    recurrence4A4Square.coeff 282 =
      -(((326600351085050430358689152 * 10 ^ 70 +
        0521701596221820382243467582019039399564134987622052959885840025263386) * 10 ^ 70 +
        8116325332156284113931686214603381843760013859405319404857999469798419) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 283,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (282 - x)) = _
  rw [show 283 = 104 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 11 +
      104 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_282_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_282_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_283_prefix_zero :
    (∑ x ∈ Finset.range 105,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (283 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (283 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_283_suffix_zero :
    (∑ x ∈ Finset.range 105,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (283 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_283 :
    recurrence4A4Square.coeff 283 =
      (((167640772833160863247047263 * 10 ^ 70 +
        4360305673167277817940981790743257446667037058393323873752334769314684) * 10 ^ 70 +
        1502267367399127798402459602720354853915635015894945106144274782991822) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 284,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (283 - x)) = _
  rw [show 284 = 105 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 10 +
      105 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_283_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_283_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_284_prefix_zero :
    (∑ x ∈ Finset.range 106,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (284 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (284 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_284_suffix_zero :
    (∑ x ∈ Finset.range 106,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (284 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_284 :
    recurrence4A4Square.coeff 284 =
      -(((65651846528189018273312465 * 10 ^ 70 +
        0222957886584490560603238205096307477561316492769620927048641016172180) * 10 ^ 70 +
        6009413692020685033269394103124955285338477129407190935236817218499485) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 285,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (284 - x)) = _
  rw [show 285 = 106 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 9 +
      106 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_284_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_284_suffix_zero]
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_319_prefix_zero :
    (∑ x ∈ Finset.range 141,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (319 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (319 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_319_suffix_zero :
    (∑ x ∈ Finset.range 141,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (319 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_319 :
    recurrence4A4Square.coeff 319 =
      ((6879651957795406699976510832241735001566260664798167803421520854403 * 10 ^ 70 +
        6755758607973274499951611465998900881878731182517666066841864170246982) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 320,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (319 - x)) = _
  rw [show 320 = 141 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 6 +
      141 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_319_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_319_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_320_prefix_zero :
    (∑ x ∈ Finset.range 142,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (320 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (320 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_320_suffix_zero :
    (∑ x ∈ Finset.range 142,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (320 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_320 :
    recurrence4A4Square.coeff 320 =
      -((1257619790909101578225125267737285745220331705219208690634265748231 * 10 ^ 70 +
        8955291507061866872370908324922494700575014894033598611280061145499406) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 321,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (320 - x)) = _
  rw [show 321 = 142 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 5 +
      142 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_320_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_320_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_321_prefix_zero :
    (∑ x ∈ Finset.range 143,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (321 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (321 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_321_suffix_zero :
    (∑ x ∈ Finset.range 143,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (321 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_321 :
    recurrence4A4Square.coeff 321 =
      ((43093688845195770101826873793510832190684740060022232964566605267 * 10 ^ 70 +
        1336624924118391473282581344612719571946692935534167434403121244439310) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 322,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (321 - x)) = _
  rw [show 322 = 143 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 4 +
      143 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_321_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_321_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_322_prefix_zero :
    (∑ x ∈ Finset.range 144,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (322 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (322 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_322_suffix_zero :
    (∑ x ∈ Finset.range 144,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (322 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_322 :
    recurrence4A4Square.coeff 322 =
      ((2070542378997992651063561879071458474900703722082548867819056129 * 10 ^ 70 +
        3035107164629534317399366510192017368819220210022712655709347152503140) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 323,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (322 - x)) = _
  rw [show 323 = 144 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 3 +
      144 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_322_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_322_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_323_prefix_zero :
    (∑ x ∈ Finset.range 145,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (323 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (323 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_323_suffix_zero :
    (∑ x ∈ Finset.range 145,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (323 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_323 :
    recurrence4A4Square.coeff 323 =
      -((188528004253068622754226673132190771963010535249132852311131787 * 10 ^ 70 +
        6117495724695797464183215322085140981318881275461415137457789904848090) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 324,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (323 - x)) = _
  rw [show 324 = 145 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 2 +
      145 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_323_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_323_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_324_prefix_zero :
    (∑ x ∈ Finset.range 146,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (324 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (324 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_324_suffix_zero :
    (∑ x ∈ Finset.range 146,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (324 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_324 :
    recurrence4A4Square.coeff 324 =
      -((294282209461227529541356883740355613760463413093657242441943 * 10 ^ 70 +
        2505205535395393955702383338255867464319680073549258799221015557447053) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 325,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (324 - x)) = _
  rw [show 325 = 146 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 1 +
      146 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_324_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_324_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_325_prefix_zero :
    (∑ x ∈ Finset.range 147,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (325 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (325 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_325_suffix_zero :
    (∑ x ∈ Finset.range 147,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (325 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_325 :
    recurrence4A4Square.coeff 325 =
      ((387459991758440756964227748700515339477852461946315865323018 * 10 ^ 70 +
        7795581671587384477151271753039012305073671087496586340841121534377198) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 326,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (325 - x)) = _
  rw [show 326 = 147 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_325_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_325_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_326_prefix_zero :
    (∑ x ∈ Finset.range 148,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (326 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (326 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_326_suffix_zero :
    (∑ x ∈ Finset.range 148,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (326 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_326 :
    recurrence4A4Square.coeff 326 =
      -((1622099580446484303211332274153952765699595652422329019029 * 10 ^ 70 +
        1651997914843532681746125682307742590705127428486541287166017442807877) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 327,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (326 - x)) = _
  rw [show 327 = 148 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 31 +
      148 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_326_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_326_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_327_prefix_zero :
    (∑ x ∈ Finset.range 149,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (327 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (327 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_327_suffix_zero :
    (∑ x ∈ Finset.range 149,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (327 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_327 :
    recurrence4A4Square.coeff 327 =
      -((582367602522785410427371681812622465169440013364389584255 * 10 ^ 70 +
        1705836699972071455456790253068250103825719056038841920499999643909290) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 328,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (327 - x)) = _
  rw [show 328 = 149 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 30 +
      149 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_327_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_327_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_328_prefix_zero :
    (∑ x ∈ Finset.range 150,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (328 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (328 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_328_suffix_zero :
    (∑ x ∈ Finset.range 150,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (328 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_328 :
    recurrence4A4Square.coeff 328 =
      -((5222435568130091972784452359487927391850341312580541986 * 10 ^ 70 +
        8837627283997237100844458352313435720050885477564169612467266025684704) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 329,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (328 - x)) = _
  rw [show 329 = 150 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 29 +
      150 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_328_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_328_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_329_prefix_zero :
    (∑ x ∈ Finset.range 151,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (329 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (329 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_329_suffix_zero :
    (∑ x ∈ Finset.range 151,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (329 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_329 :
    recurrence4A4Square.coeff 329 =
      ((514319422458267499276625972545810867513676390243094557 * 10 ^ 70 +
        0988188505378428598858164005381085095665241038359223914611692715789508) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 330,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (329 - x)) = _
  rw [show 330 = 151 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 28 +
      151 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_329_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_329_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_330_prefix_zero :
    (∑ x ∈ Finset.range 152,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (330 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (330 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_330_suffix_zero :
    (∑ x ∈ Finset.range 152,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (330 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_330 :
    recurrence4A4Square.coeff 330 =
      ((19981540052068574745668843061227113339000697637228144 * 10 ^ 70 +
        9954605277978992533872659248499959282069883241051720270753751415174055) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 331,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (330 - x)) = _
  rw [show 331 = 152 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 27 +
      152 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_330_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_330_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_331_prefix_zero :
    (∑ x ∈ Finset.range 153,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (331 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (331 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_331_suffix_zero :
    (∑ x ∈ Finset.range 153,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (331 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_331 :
    recurrence4A4Square.coeff 331 =
      ((365964004912955106747576484725887963583923522135672 * 10 ^ 70 +
        6351018308034691681083054424963318390136401442928649838977885865931266) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 332,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (331 - x)) = _
  rw [show 332 = 153 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 26 +
      153 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_331_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_331_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_332_prefix_zero :
    (∑ x ∈ Finset.range 154,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (332 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (332 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_332_suffix_zero :
    (∑ x ∈ Finset.range 154,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (332 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_332 :
    recurrence4A4Square.coeff 332 =
      ((4135499660108401371702405968273675477107181696746 * 10 ^ 70 +
        9352743612518361837932044567071682761865818296273779896436449610732726) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 333,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (332 - x)) = _
  rw [show 333 = 154 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 25 +
      154 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_332_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_332_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_333_prefix_zero :
    (∑ x ∈ Finset.range 155,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (333 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (333 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_333_suffix_zero :
    (∑ x ∈ Finset.range 155,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (333 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_333 :
    recurrence4A4Square.coeff 333 =
      ((31011430833655776944198952579161357127672736915 * 10 ^ 70 +
        1108301906702951224022436980634738492543346832272801136221677640863510) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 334,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (333 - x)) = _
  rw [show 334 = 155 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 24 +
      155 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_333_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_333_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_334_prefix_zero :
    (∑ x ∈ Finset.range 156,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (334 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (334 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_334_suffix_zero :
    (∑ x ∈ Finset.range 156,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (334 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_334 :
    recurrence4A4Square.coeff 334 =
      ((155884162685842677808667336959691517559004952 * 10 ^ 70 +
        7098626749034659390388446399978288422959462121337871826288553343472530) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 335,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (334 - x)) = _
  rw [show 335 = 156 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 23 +
      156 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_334_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_334_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_335_prefix_zero :
    (∑ x ∈ Finset.range 157,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (335 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (335 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_335_suffix_zero :
    (∑ x ∈ Finset.range 157,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (335 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_335 :
    recurrence4A4Square.coeff 335 =
      ((498735895326936922651666867774927824988637 * 10 ^ 70 +
        6909101454246856907063380220761105499588746500240178053694603934728614) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 336,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (335 - x)) = _
  rw [show 336 = 157 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 22 +
      157 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_335_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_335_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_336_prefix_zero :
    (∑ x ∈ Finset.range 158,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (336 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (336 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_336_suffix_zero :
    (∑ x ∈ Finset.range 158,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (336 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_336 :
    recurrence4A4Square.coeff 336 =
      ((788422191402604240471919215696905149419 * 10 ^ 70 +
        1964720620882930844723072421587861464813671498597170387242395354888632) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 337,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (336 - x)) = _
  rw [show 337 = 158 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 21 +
      158 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_336_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_336_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_337_prefix_zero :
    (∑ x ∈ Finset.range 159,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (337 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (337 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_337_suffix_zero :
    (∑ x ∈ Finset.range 159,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (337 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_337 :
    recurrence4A4Square.coeff 337 =
      -((713197692892228556255485419926848706 * 10 ^ 70 +
        9304319078146167847296676488297726596136315398230956650043767285787342) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 338,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (337 - x)) = _
  rw [show 338 = 159 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 20 +
      159 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_337_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_337_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_338_prefix_zero :
    (∑ x ∈ Finset.range 160,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (338 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (338 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_338_suffix_zero :
    (∑ x ∈ Finset.range 160,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (338 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_338 :
    recurrence4A4Square.coeff 338 =
      -((6597078588303681490384788537951714 * 10 ^ 70 +
        1561141312029677125454368453577217449159168961830509056385891328383362) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 339,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (338 - x)) = _
  rw [show 339 = 160 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 19 +
      160 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_338_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_338_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_339_prefix_zero :
    (∑ x ∈ Finset.range 161,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (339 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (339 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_339_suffix_zero :
    (∑ x ∈ Finset.range 161,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (339 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_339 :
    recurrence4A4Square.coeff 339 =
      -((13870585199136708050228178391108 * 10 ^ 70 +
        3357640084507328667026464295002777761307829931983888115692153854641910) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 340,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (339 - x)) = _
  rw [show 340 = 161 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 18 +
      161 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_339_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_339_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_340_prefix_zero :
    (∑ x ∈ Finset.range 162,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (340 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (340 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_340_suffix_zero :
    (∑ x ∈ Finset.range 162,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (340 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_340 :
    recurrence4A4Square.coeff 340 =
      -((8841789082681546770235451228 * 10 ^ 70 +
        7968194793544480289873177822745798998221347372224465960387362181727028) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 341,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (340 - x)) = _
  rw [show 341 = 162 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 17 +
      162 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_340_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_340_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_341_prefix_zero :
    (∑ x ∈ Finset.range 163,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (341 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (341 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_341_suffix_zero :
    (∑ x ∈ Finset.range 163,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (341 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_341 :
    recurrence4A4Square.coeff 341 =
      ((17057135479476206256634696 * 10 ^ 70 +
        1017222792145342949002754567156161117275414137041804849700262135547220) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 342,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (341 - x)) = _
  rw [show 342 = 163 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 16 +
      163 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_341_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_341_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_342_prefix_zero :
    (∑ x ∈ Finset.range 164,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (342 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (342 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_342_suffix_zero :
    (∑ x ∈ Finset.range 164,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (342 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_342 :
    recurrence4A4Square.coeff 342 =
      ((44592042870203709611942 * 10 ^ 70 +
        3511932960808022206290932812189882647088051191860661292981576646655999) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 343,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (342 - x)) = _
  rw [show 343 = 164 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 15 +
      164 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_342_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_342_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_343_prefix_zero :
    (∑ x ∈ Finset.range 165,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (343 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (343 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_343_suffix_zero :
    (∑ x ∈ Finset.range 165,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (343 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_343 :
    recurrence4A4Square.coeff 343 =
      ((46478067118278524275 * 10 ^ 70 +
        8408250256520402828523525550669930281037760203882056647468301010344308) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 344,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (343 - x)) = _
  rw [show 344 = 165 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 14 +
      165 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_343_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_343_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_344_prefix_zero :
    (∑ x ∈ Finset.range 166,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (344 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (344 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_344_suffix_zero :
    (∑ x ∈ Finset.range 166,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (344 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_344 :
    recurrence4A4Square.coeff 344 =
      ((26815579655532077 * 10 ^ 70 +
        7246795778406707859482058756966909352451749872423681619003560223635325) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 345,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (344 - x)) = _
  rw [show 345 = 166 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 13 +
      166 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_344_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_344_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_345_prefix_zero :
    (∑ x ∈ Finset.range 167,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (345 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (345 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_345_suffix_zero :
    (∑ x ∈ Finset.range 167,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (345 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_345 :
    recurrence4A4Square.coeff 345 =
      ((8994751079290 * 10 ^ 70 +
        9676088662409391965397422361705638564494022782934929096940758026374270) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 346,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (345 - x)) = _
  rw [show 346 = 167 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 12 +
      167 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_345_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_345_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_346_prefix_zero :
    (∑ x ∈ Finset.range 168,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (346 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (346 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_346_suffix_zero :
    (∑ x ∈ Finset.range 168,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (346 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_346 :
    recurrence4A4Square.coeff 346 =
      ((1744366891 * 10 ^ 70 +
        3088183840292621173402735344186274387874458499970562653214501564693674) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 347,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (346 - x)) = _
  rw [show 347 = 168 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 11 +
      168 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_346_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_346_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_347_prefix_zero :
    (∑ x ∈ Finset.range 169,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (347 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (347 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_347_suffix_zero :
    (∑ x ∈ Finset.range 169,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (347 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_347 :
    recurrence4A4Square.coeff 347 =
      ((189655 * 10 ^ 70 +
        5541206303811756361868383890594524590284187969400259529138816582695862) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 348,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (347 - x)) = _
  rw [show 348 = 169 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 10 +
      169 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_347_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_347_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_348_prefix_zero :
    (∑ x ∈ Finset.range 170,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (348 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (348 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_348_suffix_zero :
    (∑ x ∈ Finset.range 170,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (348 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_348 :
    recurrence4A4Square.coeff 348 =
      ((11 * 10 ^ 70 +
        1118152040355336922123889324615966148225058072231422799739216906330957) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 349,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (348 - x)) = _
  rw [show 349 = 170 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 9 +
      170 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_348_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_348_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_349_prefix_zero :
    (∑ x ∈ Finset.range 171,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (349 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (349 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_349_suffix_zero :
    (∑ x ∈ Finset.range 171,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (349 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_349 :
    recurrence4A4Square.coeff 349 =
      (3294187829126525658111999044906005665122417868950220234815569550036 : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 350,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (349 - x)) = _
  rw [show 350 = 171 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 8 +
      171 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_349_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_349_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_350_prefix_zero :
    (∑ x ∈ Finset.range 172,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (350 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (350 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_350_suffix_zero :
    (∑ x ∈ Finset.range 172,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (350 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_350 :
    recurrence4A4Square.coeff 350 =
      (46761195054975912432022141342913210693235416615085836269304792 : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 351,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (350 - x)) = _
  rw [show 351 = 172 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 7 +
      172 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_350_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_350_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_351_prefix_zero :
    (∑ x ∈ Finset.range 173,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (351 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (351 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_351_suffix_zero :
    (∑ x ∈ Finset.range 173,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (351 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_351 :
    recurrence4A4Square.coeff 351 =
      (282228363208519389703829178132802097983214024899202160594 : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 352,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (351 - x)) = _
  rw [show 352 = 173 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 6 +
      173 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_351_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_351_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_352_prefix_zero :
    (∑ x ∈ Finset.range 174,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (352 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (352 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_352_suffix_zero :
    (∑ x ∈ Finset.range 174,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (352 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_352 :
    recurrence4A4Square.coeff 352 =
      (688588957607202701068994497847406833908335977217771 : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 353,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (352 - x)) = _
  rw [show 353 = 174 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 5 +
      174 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_352_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_352_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_353_prefix_zero :
    (∑ x ∈ Finset.range 175,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (353 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (353 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_353_suffix_zero :
    (∑ x ∈ Finset.range 175,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (353 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_353 :
    recurrence4A4Square.coeff 353 =
      (510094750000584395586589881327884907544173790 : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 354,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (353 - x)) = _
  rw [show 354 = 175 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 4 +
      175 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_353_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_353_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_354_prefix_zero :
    (∑ x ∈ Finset.range 176,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (354 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (354 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_354_suffix_zero :
    (∑ x ∈ Finset.range 176,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (354 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_354 :
    recurrence4A4Square.coeff 354 =
      (121790380541980693795330736786246777411 : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 355,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (354 - x)) = _
  rw [show 355 = 176 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 3 +
      176 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_354_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_354_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_355_prefix_zero :
    (∑ x ∈ Finset.range 177,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (355 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (355 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_355_suffix_zero :
    (∑ x ∈ Finset.range 177,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (355 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_355 :
    recurrence4A4Square.coeff 355 =
      (3261532994918344993998095763390 : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 356,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (355 - x)) = _
  rw [show 356 = 177 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 2 +
      177 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_355_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_355_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_356_prefix_zero :
    (∑ x ∈ Finset.range 178,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (356 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (356 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_356_suffix_zero :
    (∑ x ∈ Finset.range 178,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (356 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_356 :
    recurrence4A4Square.coeff 356 =
      (23215239933528791584969 : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 357,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (356 - x)) = _
  rw [show 357 = 178 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 1 +
      178 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_356_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_356_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
