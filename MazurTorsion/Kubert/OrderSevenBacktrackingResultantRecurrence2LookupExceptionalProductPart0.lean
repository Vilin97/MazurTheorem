/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupA6Square
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupExceptional
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: ExceptionalProduct coefficient convolution

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence2A6Square_coeff_0
  recurrence2A6Square_coeff_1
  recurrence2A6Square_coeff_2
  recurrence2A6Square_coeff_3
  recurrence2A6Square_coeff_4
  recurrence2A6Square_coeff_5
  recurrence2A6Square_coeff_6
  recurrence2A6Square_coeff_7
  recurrence2A6Square_coeff_8
  recurrence2A6Square_coeff_9
  recurrence2A6Square_coeff_10
  recurrence2A6Square_coeff_11
  recurrence2A6Square_coeff_12
  recurrence2A6Square_coeff_13
  recurrence2A6Square_coeff_14
  recurrence2A6Square_coeff_15
  recurrence2A6Square_coeff_16
  recurrence2A6Square_coeff_17
  recurrence2A6Square_coeff_18
  recurrence2A6Square_coeff_19
  recurrence2A6Square_coeff_20
  recurrence2A6Square_coeff_21
  recurrence2A6Square_coeff_22
  recurrence2A6Square_coeff_23
  recurrence2A6Square_coeff_24
  recurrence2A6Square_coeff_25
  recurrence2A6Square_coeff_26
  recurrence2A6Square_coeff_27
  recurrence2A6Square_coeff_28
  recurrence2A6Square_coeff_29
  recurrence2A6Square_coeff_30
  recurrence2A6Square_coeff_31
  recurrence2A6Square_coeff_32
  recurrence2A6Square_coeff_33
  recurrence2A6Square_coeff_34
  recurrence2A6Square_coeff_35
  recurrence2A6Square_coeff_36
  recurrence2A6Square_coeff_37
  recurrence2A6Square_coeff_38
  recurrence2A6Square_coeff_39
  recurrence2A6Square_coeff_40
  recurrence2A6Square_coeff_41
  recurrence2A6Square_coeff_42
  recurrence2A6Square_coeff_43
  recurrence2A6Square_coeff_44
  recurrence2A6Square_coeff_45
  recurrence2A6Square_coeff_46
  recurrence2A6Square_coeff_47
  recurrence2A6Square_coeff_48
  recurrence2A6Square_coeff_49
  recurrence2A6Square_coeff_50
  recurrence2A6Square_coeff_51
  recurrence2A6Square_coeff_52
  recurrence2A6Square_coeff_53
  recurrence2A6Square_coeff_54
  recurrence2A6Square_coeff_55
  recurrence2A6Square_coeff_56
  recurrence2A6Square_coeff_57
  recurrence2A6Square_coeff_58
  recurrence2A6Square_coeff_59
  recurrence2A6Square_coeff_60
  recurrence2A6Square_coeff_61
  recurrence2A6Square_coeff_62
  recurrence2A6Square_coeff_63
  recurrence2A6Square_coeff_64
  recurrence2A6Square_coeff_65
  recurrence2A6Square_coeff_66
  recurrence2A6Square_coeff_67
  recurrence2A6Square_coeff_68
  recurrence2A6Square_coeff_69
  recurrence2A6Square_coeff_70
  recurrence2A6Square_coeff_71
  recurrence2A6Square_coeff_72
  recurrence2A6Square_coeff_73
  recurrence2A6Square_coeff_74
  recurrence2A6Square_coeff_75
  recurrence2A6Square_coeff_76
  recurrence2A6Square_coeff_77
  recurrence2A6Square_coeff_78
  recurrence2A6Square_coeff_79
  recurrence2A6Square_coeff_80
  recurrence2A6Square_coeff_81
  recurrence2A6Square_coeff_82
  recurrence2A6Square_coeff_83
  recurrence2A6Square_coeff_84
  recurrence2A6Square_coeff_85
  recurrence2A6Square_coeff_86
  recurrence2A6Square_coeff_87
  recurrence2A6Square_coeff_88
  recurrence2A6Square_coeff_89
  recurrence2A6Square_coeff_90
  recurrence2A6Square_coeff_91
  recurrence2A6Square_coeff_92
  recurrence2A6Square_coeff_93
  recurrence2A6Square_coeff_94
  recurrence2A6Square_coeff_95
  recurrence2A6Square_coeff_96
  recurrence2A6Square_coeff_97
  recurrence2A6Square_coeff_98
  recurrence2A6Square_coeff_99
  recurrence2A6Square_coeff_100
  recurrence2A6Square_coeff_101
  recurrence2A6Square_coeff_102
  recurrence2A6Square_coeff_103
  recurrence2A6Square_coeff_104
  recurrence2A6Square_coeff_105
  recurrence2A6Square_coeff_106
  recurrence2A6Square_coeff_107
  recurrence2A6Square_coeff_108
  recurrence2A6Square_coeff_109
  recurrence2A6Square_coeff_110
  recurrence2A6Square_coeff_111
  recurrence2A6Square_coeff_112
  recurrence2A6Square_coeff_113
  recurrence2A6Square_coeff_114
  recurrence2A6Square_coeff_115
  recurrence2A6Square_coeff_116
  recurrence2A6Square_coeff_117
  recurrence2A6Square_coeff_118
  recurrence2A6Square_coeff_119
  recurrence2A6Square_coeff_120
  recurrence2A6Square_coeff_121
  recurrence2A6Square_coeff_122
  recurrence2A6Square_coeff_123
  recurrence2A6Square_coeff_124
  recurrence2A6Square_coeff_125
  recurrence2A6Square_coeff_126
  recurrence2A6Square_coeff_127
  recurrence2A6Square_coeff_128
  recurrence2A6Square_coeff_129
  recurrence2A6Square_coeff_130
  recurrence2A6Square_coeff_131
  recurrence2A6Square_coeff_132
  recurrence2A6Square_coeff_133
  recurrence2A6Square_coeff_134
  recurrence2A6Square_coeff_135
  recurrence2A6Square_coeff_136
  recurrence2A6Square_coeff_137
  recurrence2A6Square_coeff_138
  recurrence2A6Square_coeff_139
  recurrence2A6Square_coeff_140
  recurrence2A6Square_coeff_141
  recurrence2A6Square_coeff_142
  recurrence2A6Square_coeff_143
  recurrence2A6Square_coeff_144
  recurrence2A6Square_coeff_145
  recurrence2A6Square_coeff_146
  recurrence2A6Square_coeff_147
  recurrence2A6Square_coeff_148
  recurrence2A6Square_coeff_149
  recurrence2A6Square_coeff_150
  recurrence2A6Square_coeff_151
  recurrence2A6Square_coeff_152
  recurrence2A6Square_coeff_153
  recurrence2A6Square_coeff_154
  recurrence2A6Square_coeff_155
  recurrence2A6Square_coeff_156
  recurrence2A6Square_coeff_157
  recurrence2A6Square_coeff_158
  recurrence2A6Square_coeff_159
  recurrence2A6Square_coeff_160
  recurrence2A6Square_coeff_161
  recurrence2A6Square_coeff_162
  recurrence2A6Square_coeff_163
  recurrence2A6Square_coeff_164
  recurrence2A6Square_coeff_165
  recurrence2A6Square_coeff_166
  recurrence2A6Square_coeff_167
  recurrence2A6Square_coeff_168
  recurrence2A6Square_coeff_169
  recurrence2A6Square_coeff_170
  recurrence2A6Square_coeff_171
  recurrence2A6Square_coeff_172
  recurrence2A6Square_coeff_173
  recurrence2A6Square_coeff_174
  recurrence2A6Square_coeff_175
  recurrence2A6Square_coeff_176
  recurrence2A6Square_coeff_177
  recurrence2A6Square_coeff_178
  recurrence2A6Square_coeff_179
  recurrence2A6Square_coeff_180
  recurrence2A6Square_coeff_181
  recurrence2A6Square_coeff_182
  recurrence2A6Square_coeff_183
  recurrence2A6Square_coeff_184
  recurrence2A6Square_coeff_185
  recurrence2A6Square_coeff_186
  recurrence2A6Square_coeff_187
  recurrence2A6Square_coeff_188
  recurrence2A6Square_coeff_189
  recurrence2A6Square_coeff_190
  recurrence2Exceptional_coeff_0
  recurrence2Exceptional_coeff_1
  recurrence2Exceptional_coeff_2
  recurrence2Exceptional_coeff_3

theorem recurrence2ExceptionalProduct_coeff_0 :
    recurrence2ExceptionalProduct.coeff 0 =
      (0 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 1 = 0 +
    1 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 1 = 1 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2ExceptionalProduct_coeff_1 :
    recurrence2ExceptionalProduct.coeff 1 =
      (0 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 2 = 0 +
    2 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 2 = 2 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2ExceptionalProduct_coeff_2 :
    recurrence2ExceptionalProduct.coeff 2 =
      (-367236 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 3 = 0 +
    3 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2ExceptionalProduct_coeff_3 :
    recurrence2ExceptionalProduct.coeff 3 =
      (-320066172 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 4 = 0 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_4_prefix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence2A6Square.coeff x * exceptional2.coeff (4 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (4 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_4 :
    recurrence2ExceptionalProduct.coeff 4 =
      (726546325632 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 5 = 1 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_4_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_5_prefix_zero :
    (∑ x ∈ Finset.range 2,
      recurrence2A6Square.coeff x * exceptional2.coeff (5 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (5 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_5 :
    recurrence2ExceptionalProduct.coeff 5 =
      (293748497931840 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 6 = 2 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_5_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_6_prefix_zero :
    (∑ x ∈ Finset.range 3,
      recurrence2A6Square.coeff x * exceptional2.coeff (6 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (6 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_6 :
    recurrence2ExceptionalProduct.coeff 6 =
      (-464414710975843852 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 7 = 3 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_6_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_7_prefix_zero :
    (∑ x ∈ Finset.range 4,
      recurrence2A6Square.coeff x * exceptional2.coeff (7 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (7 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_7 :
    recurrence2ExceptionalProduct.coeff 7 =
      (53864452136449766196 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 8 = 4 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_7_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_8_prefix_zero :
    (∑ x ∈ Finset.range 5,
      recurrence2A6Square.coeff x * exceptional2.coeff (8 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (8 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_8 :
    recurrence2ExceptionalProduct.coeff 8 =
      (8580322044044475318048 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 9 = 5 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_8_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_9_prefix_zero :
    (∑ x ∈ Finset.range 6,
      recurrence2A6Square.coeff x * exceptional2.coeff (9 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (9 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_9 :
    recurrence2ExceptionalProduct.coeff 9 =
      (-1001453366418884843606568 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 10 = 6 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_9_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_10_prefix_zero :
    (∑ x ∈ Finset.range 7,
      recurrence2A6Square.coeff x * exceptional2.coeff (10 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (10 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_10 :
    recurrence2ExceptionalProduct.coeff 10 =
      (-64252976984225032604588313 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 11 = 7 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_10_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_11_prefix_zero :
    (∑ x ∈ Finset.range 8,
      recurrence2A6Square.coeff x * exceptional2.coeff (11 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (11 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_11 :
    recurrence2ExceptionalProduct.coeff 11 =
      (5452970601589238298142705045 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 12 = 8 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_11_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_12_prefix_zero :
    (∑ x ∈ Finset.range 9,
      recurrence2A6Square.coeff x * exceptional2.coeff (12 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (12 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_12 :
    recurrence2ExceptionalProduct.coeff 12 =
      (234364405905702466757098034684 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 13 = 9 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_12_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_13_prefix_zero :
    (∑ x ∈ Finset.range 10,
      recurrence2A6Square.coeff x * exceptional2.coeff (13 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (13 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_13 :
    recurrence2ExceptionalProduct.coeff 13 =
      (-10831583456008651287292133283792 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 14 = 10 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_13_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_14_prefix_zero :
    (∑ x ∈ Finset.range 11,
      recurrence2A6Square.coeff x * exceptional2.coeff (14 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (14 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_14 :
    recurrence2ExceptionalProduct.coeff 14 =
      (-532714846177645343055757957864660 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 15 = 11 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_14_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_15_prefix_zero :
    (∑ x ∈ Finset.range 12,
      recurrence2A6Square.coeff x * exceptional2.coeff (15 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (15 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_15 :
    recurrence2ExceptionalProduct.coeff 15 =
      (8187876999495614449250817161580580 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 16 = 12 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_15_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_16_prefix_zero :
    (∑ x ∈ Finset.range 13,
      recurrence2A6Square.coeff x * exceptional2.coeff (16 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (16 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_16 :
    recurrence2ExceptionalProduct.coeff 16 =
      (655462633793904002454813954733517428 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 17 = 13 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_16_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_17_prefix_zero :
    (∑ x ∈ Finset.range 14,
      recurrence2A6Square.coeff x * exceptional2.coeff (17 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (17 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_17 :
    recurrence2ExceptionalProduct.coeff 17 =
      (1254943686434167520935030100967300032 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 18 = 14 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_17_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_18_prefix_zero :
    (∑ x ∈ Finset.range 15,
      recurrence2A6Square.coeff x * exceptional2.coeff (18 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (18 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_18 :
    recurrence2ExceptionalProduct.coeff 18 =
      (-431604430997692370886068060436844971276 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 19 = 15 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_18_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_19_prefix_zero :
    (∑ x ∈ Finset.range 16,
      recurrence2A6Square.coeff x * exceptional2.coeff (19 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (19 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_19 :
    recurrence2ExceptionalProduct.coeff 19 =
      (-5759130543607096172110135860926818550508 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 20 = 16 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_19_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_20_prefix_zero :
    (∑ x ∈ Finset.range 17,
      recurrence2A6Square.coeff x * exceptional2.coeff (20 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (20 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_20 :
    recurrence2ExceptionalProduct.coeff 20 =
      (139455335874789394051382244505329667376498 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 21 = 17 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_20_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_21_prefix_zero :
    (∑ x ∈ Finset.range 18,
      recurrence2A6Square.coeff x * exceptional2.coeff (21 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (21 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_21 :
    recurrence2ExceptionalProduct.coeff 21 =
      (3832676783471946320679822029723045573855560 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 22 = 18 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_21_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_22_prefix_zero :
    (∑ x ∈ Finset.range 19,
      recurrence2A6Square.coeff x * exceptional2.coeff (22 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (22 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_22 :
    recurrence2ExceptionalProduct.coeff 22 =
      (-10361801064580706182287348275790192104357274 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 23 = 19 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_22_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_23_prefix_zero :
    (∑ x ∈ Finset.range 20,
      recurrence2A6Square.coeff x * exceptional2.coeff (23 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (23 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_23 :
    recurrence2ExceptionalProduct.coeff 23 =
      (-1241133528661695456966297010467235357473406188 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 24 = 20 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_23_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_24_prefix_zero :
    (∑ x ∈ Finset.range 21,
      recurrence2A6Square.coeff x * exceptional2.coeff (24 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (24 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_24 :
    recurrence2ExceptionalProduct.coeff 24 =
      (-8336013200853651481157214035047331126217786224 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 25 = 21 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_24_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_25_prefix_zero :
    (∑ x ∈ Finset.range 22,
      recurrence2A6Square.coeff x * exceptional2.coeff (25 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (25 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_25 :
    recurrence2ExceptionalProduct.coeff 25 =
      (219766367495676034433559725442115466829645150974 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 26 = 22 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_25_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_26_prefix_zero :
    (∑ x ∈ Finset.range 23,
      recurrence2A6Square.coeff x * exceptional2.coeff (26 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (26 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_26 :
    recurrence2ExceptionalProduct.coeff 26 =
      (3350547321296009101461884977055609408352809866324 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 27 = 23 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_26_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_27_prefix_zero :
    (∑ x ∈ Finset.range 24,
      recurrence2A6Square.coeff x * exceptional2.coeff (27 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (27 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_27 :
    recurrence2ExceptionalProduct.coeff 27 =
      (-15671492776784366117862057166505053487802614760230 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 28 = 24 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_27_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_28_prefix_zero :
    (∑ x ∈ Finset.range 25,
      recurrence2A6Square.coeff x * exceptional2.coeff (28 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (28 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_28 :
    recurrence2ExceptionalProduct.coeff 28 =
      (-653853008246548467203894962436503424735444345739462 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 29 = 25 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_28_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_29_prefix_zero :
    (∑ x ∈ Finset.range 26,
      recurrence2A6Square.coeff x * exceptional2.coeff (29 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (29 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_29 :
    recurrence2ExceptionalProduct.coeff 29 =
      (-1669107412922621511183069451092319398596471171290566 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 30 = 26 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_29_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_30_prefix_zero :
    (∑ x ∈ Finset.range 27,
      recurrence2A6Square.coeff x * exceptional2.coeff (30 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (30 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_30 :
    recurrence2ExceptionalProduct.coeff 30 =
      (76769740752737525756169103484344860861448719813644719 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 31 = 27 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_30_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_31_prefix_zero :
    (∑ x ∈ Finset.range 28,
      recurrence2A6Square.coeff x * exceptional2.coeff (31 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (31 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_31 :
    recurrence2ExceptionalProduct.coeff 31 =
      (611460189620752895913540969883175876842161412110398055 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 32 = 28 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_31_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_32_prefix_zero :
    (∑ x ∈ Finset.range 29,
      recurrence2A6Square.coeff x * exceptional2.coeff (32 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (32 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_32 :
    recurrence2ExceptionalProduct.coeff 32 =
      (-5517963228067169191289274706169170522476232483488244689 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 33 = 29 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_32_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_33_prefix_zero :
    (∑ x ∈ Finset.range 30,
      recurrence2A6Square.coeff x * exceptional2.coeff (33 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (33 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_33 :
    recurrence2ExceptionalProduct.coeff 33 =
      (-86325214978043221947437868116250845948823825918570161983 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 34 = 30 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_33_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_34_prefix_zero :
    (∑ x ∈ Finset.range 31,
      recurrence2A6Square.coeff x * exceptional2.coeff (34 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (34 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_34 :
    recurrence2ExceptionalProduct.coeff 34 =
      (151143706355058743306980491546291952167591967094064241618 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 35 = 31 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_34_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_35_prefix_zero :
    (∑ x ∈ Finset.range 32,
      recurrence2A6Square.coeff x * exceptional2.coeff (35 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (35 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_35 :
    recurrence2ExceptionalProduct.coeff 35 =
      (7998617371108576359967507365059461863986472312980998358368 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 36 = 32 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_35_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_36_prefix_zero :
    (∑ x ∈ Finset.range 33,
      recurrence2A6Square.coeff x * exceptional2.coeff (36 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (36 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_36 :
    recurrence2ExceptionalProduct.coeff 36 =
      (16074338672650160990198592499503640428494909878081203046756 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 37 = 33 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_36_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_37_prefix_zero :
    (∑ x ∈ Finset.range 34,
      recurrence2A6Square.coeff x * exceptional2.coeff (37 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (37 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_37 :
    recurrence2ExceptionalProduct.coeff 37 =
      (-536566015595370252368194826012537429588602445028342825188526 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 38 = 34 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_37_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_38_prefix_zero :
    (∑ x ∈ Finset.range 35,
      recurrence2A6Square.coeff x * exceptional2.coeff (38 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (38 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_38 :
    recurrence2ExceptionalProduct.coeff 38 =
      (-2695168151331901135135417541265380450499938991112532667180766 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 39 = 35 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_38_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_39_prefix_zero :
    (∑ x ∈ Finset.range 36,
      recurrence2A6Square.coeff x * exceptional2.coeff (39 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (39 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_39 :
    recurrence2ExceptionalProduct.coeff 39 =
      (27053083693333196854760042837152451500730060821000440806073410 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 40 = 36 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_39_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_40_prefix_zero :
    (∑ x ∈ Finset.range 37,
      recurrence2A6Square.coeff x * exceptional2.coeff (40 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (40 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_40 :
    recurrence2ExceptionalProduct.coeff 40 =
      (227709230781144031353179555547601143071269686408217307801312501 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 41 = 37 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_40_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_41_prefix_zero :
    (∑ x ∈ Finset.range 38,
      recurrence2A6Square.coeff x * exceptional2.coeff (41 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (41 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_41 :
    recurrence2ExceptionalProduct.coeff 41 =
      (-1006880818712974624959799323030566991273474193270998827493683331 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 42 = 38 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_41_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_42_prefix_zero :
    (∑ x ∈ Finset.range 39,
      recurrence2A6Square.coeff x * exceptional2.coeff (42 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (42 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_42 :
    recurrence2ExceptionalProduct.coeff 42 =
      (-14017139639256106867352550309066383600060086814430277992385815633 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 43 = 39 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_42_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_43_prefix_zero :
    (∑ x ∈ Finset.range 40,
      recurrence2A6Square.coeff x * exceptional2.coeff (43 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (43 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_43 :
    recurrence2ExceptionalProduct.coeff 43 =
      (24423140247470161044550549161331275664112238919786188312934930987 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 44 = 40 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_43_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_44_prefix_zero :
    (∑ x ∈ Finset.range 41,
      recurrence2A6Square.coeff x * exceptional2.coeff (44 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (44 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_44 :
    recurrence2ExceptionalProduct.coeff 44 =
      (693269486216798461042119947394830875480048225958416689677407198556 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 45 = 41 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_44_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_45_prefix_zero :
    (∑ x ∈ Finset.range 42,
      recurrence2A6Square.coeff x * exceptional2.coeff (45 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (45 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_45 :
    recurrence2ExceptionalProduct.coeff 45 =
      (-78607444671217781145927345181450305385976261764762533653667880804 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 46 = 42 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_45_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_46_prefix_zero :
    (∑ x ∈ Finset.range 43,
      recurrence2A6Square.coeff x * exceptional2.coeff (46 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (46 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_46 :
    recurrence2ExceptionalProduct.coeff 46 =
      (-28942120752221119530208836225732924349667112231940773036924630743853 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 47 = 43 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_46_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_47_prefix_zero :
    (∑ x ∈ Finset.range 44,
      recurrence2A6Square.coeff x * exceptional2.coeff (47 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (47 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_47 :
    recurrence2ExceptionalProduct.coeff 47 =
      (-28670640541775414514497327493362329549653840313889590302088579814633 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 48 = 44 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_47_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_48_prefix_zero :
    (∑ x ∈ Finset.range 45,
      recurrence2A6Square.coeff x * exceptional2.coeff (48 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (48 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_48 :
    recurrence2ExceptionalProduct.coeff 48 =
      (1053189151656227946905877737195340657120845365791854701988202090459744 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 49 = 45 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_48_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_49_prefix_zero :
    (∑ x ∈ Finset.range 46,
      recurrence2A6Square.coeff x * exceptional2.coeff (49 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (49 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_49 :
    recurrence2ExceptionalProduct.coeff 49 =
      (1848672307114596625622773663470838921741823118673852382128625451972936 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 50 = 46 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_49_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_50_prefix_zero :
    (∑ x ∈ Finset.range 47,
      recurrence2A6Square.coeff x * exceptional2.coeff (50 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (50 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_50 :
    recurrence2ExceptionalProduct.coeff 50 =
      -((3 * 10 ^ 70 +
        4238504622762320631545766898075064358161833380722524169134905083307382) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 51 = 47 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_50_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_51_prefix_zero :
    (∑ x ∈ Finset.range 48,
      recurrence2A6Square.coeff x * exceptional2.coeff (51 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (51 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_51 :
    recurrence2ExceptionalProduct.coeff 51 =
      -((7 * 10 ^ 70 +
        6737701699620924854239376231166016443445272835624928053131374791938532) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 52 = 48 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_51_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_52_prefix_zero :
    (∑ x ∈ Finset.range 49,
      recurrence2A6Square.coeff x * exceptional2.coeff (52 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (52 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_52 :
    recurrence2ExceptionalProduct.coeff 52 =
      ((101 * 10 ^ 70 +
        3804516520198809766426517839361923322890771393422285007446553548135950) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 53 = 49 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_52_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_53_prefix_zero :
    (∑ x ∈ Finset.range 50,
      recurrence2A6Square.coeff x * exceptional2.coeff (53 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (53 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_53 :
    recurrence2ExceptionalProduct.coeff 53 =
      ((249 * 10 ^ 70 +
        2568898441810445993097849386336078543546325161264972178007859325751454) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 54 = 50 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_53_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_54_prefix_zero :
    (∑ x ∈ Finset.range 51,
      recurrence2A6Square.coeff x * exceptional2.coeff (54 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (54 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_54 :
    recurrence2ExceptionalProduct.coeff 54 =
      -((2772 * 10 ^ 70 +
        7937563601633934802066951637527271535668279367939559965003700168726169) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 55 = 51 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_54_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_55_prefix_zero :
    (∑ x ∈ Finset.range 52,
      recurrence2A6Square.coeff x * exceptional2.coeff (55 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (55 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_55 :
    recurrence2ExceptionalProduct.coeff 55 =
      -((6675 * 10 ^ 70 +
        1304309640768173553864473582897949977506641461264696234781264777062801) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 56 = 52 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_55_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_56_prefix_zero :
    (∑ x ∈ Finset.range 53,
      recurrence2A6Square.coeff x * exceptional2.coeff (56 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (56 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_56 :
    recurrence2ExceptionalProduct.coeff 56 =
      ((70588 * 10 ^ 70 +
        7349919748570618429594007726709067918101628468315596866490912694278575) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 57 = 53 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_56_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_57_prefix_zero :
    (∑ x ∈ Finset.range 54,
      recurrence2A6Square.coeff x * exceptional2.coeff (57 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (57 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_57 :
    recurrence2ExceptionalProduct.coeff 57 =
      ((148521 * 10 ^ 70 +
        3536335445904406197975000411239827629840919665359469205089508004112205) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 58 = 54 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_57_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_58_prefix_zero :
    (∑ x ∈ Finset.range 55,
      recurrence2A6Square.coeff x * exceptional2.coeff (58 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (58 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_58 :
    recurrence2ExceptionalProduct.coeff 58 =
      -((1673780 * 10 ^ 70 +
        9622629112029994783671948485944220322856317131546633742576069581734384) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 59 = 55 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_58_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_59_prefix_zero :
    (∑ x ∈ Finset.range 56,
      recurrence2A6Square.coeff x * exceptional2.coeff (59 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (59 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_59 :
    recurrence2ExceptionalProduct.coeff 59 =
      -((2661734 * 10 ^ 70 +
        1269737702488570588164724183096262034415794347097890790864423118540682) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 60 = 56 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_59_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_60_prefix_zero :
    (∑ x ∈ Finset.range 57,
      recurrence2A6Square.coeff x * exceptional2.coeff (60 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (60 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_60 :
    recurrence2ExceptionalProduct.coeff 60 =
      ((36747872 * 10 ^ 70 +
        0089758904007966451163450240273591178212239510854208029126379766946903) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 61 = 57 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_60_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_61_prefix_zero :
    (∑ x ∈ Finset.range 58,
      recurrence2A6Square.coeff x * exceptional2.coeff (61 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (61 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_61 :
    recurrence2ExceptionalProduct.coeff 61 =
      ((33845104 * 10 ^ 70 +
        0545517841041143494956880855647896149185408669081758599286560926387325) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 62 = 58 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_61_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_62_prefix_zero :
    (∑ x ∈ Finset.range 59,
      recurrence2A6Square.coeff x * exceptional2.coeff (62 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (62 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_62 :
    recurrence2ExceptionalProduct.coeff 62 =
      -((738502534 * 10 ^ 70 +
        3399259809637285496100184205048660088590843009876757360402316490357902) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 63 = 59 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_62_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_63_prefix_zero :
    (∑ x ∈ Finset.range 60,
      recurrence2A6Square.coeff x * exceptional2.coeff (63 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (63 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_63 :
    recurrence2ExceptionalProduct.coeff 63 =
      -((105061558 * 10 ^ 70 +
        5201104378695760487275170670034061190954112058173239552280028445688814) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 64 = 60 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_63_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_64_prefix_zero :
    (∑ x ∈ Finset.range 61,
      recurrence2A6Square.coeff x * exceptional2.coeff (64 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (64 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_64 :
    recurrence2ExceptionalProduct.coeff 64 =
      ((13362160826 * 10 ^ 70 +
        4139518628531256106591985764703543033371151522876684515551956011081868) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 65 = 61 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_64_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_65_prefix_zero :
    (∑ x ∈ Finset.range 62,
      recurrence2A6Square.coeff x * exceptional2.coeff (65 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (65 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_65 :
    recurrence2ExceptionalProduct.coeff 65 =
      -((9768872450 * 10 ^ 70 +
        7040722305791370676066450029182165982489750239513989448941836339938980) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 66 = 62 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_65_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_66_prefix_zero :
    (∑ x ∈ Finset.range 63,
      recurrence2A6Square.coeff x * exceptional2.coeff (66 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (66 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_66 :
    recurrence2ExceptionalProduct.coeff 66 =
      -((212655203318 * 10 ^ 70 +
        9881063386516234362404857046076157850904205596225588045068957867132627) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 67 = 63 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_66_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_67_prefix_zero :
    (∑ x ∈ Finset.range 64,
      recurrence2A6Square.coeff x * exceptional2.coeff (67 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (67 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_67 :
    recurrence2ExceptionalProduct.coeff 67 =
      ((369915202308 * 10 ^ 70 +
        6636879278024935520559721130387744102341673436026026134625213406997629) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 68 = 64 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_67_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_68_prefix_zero :
    (∑ x ∈ Finset.range 65,
      recurrence2A6Square.coeff x * exceptional2.coeff (68 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (68 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_68 :
    recurrence2ExceptionalProduct.coeff 68 =
      ((2867656201935 * 10 ^ 70 +
        4711253799452211321061851142625370492088352593652383029770385937380424) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 69 = 65 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_68_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_69_prefix_zero :
    (∑ x ∈ Finset.range 66,
      recurrence2A6Square.coeff x * exceptional2.coeff (69 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (69 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_69 :
    recurrence2ExceptionalProduct.coeff 69 =
      -((8718389395549 * 10 ^ 70 +
        1633196620911875573827157284347192956461348858594534521058488703460406) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 70 = 66 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_69_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_70_prefix_zero :
    (∑ x ∈ Finset.range 67,
      recurrence2A6Square.coeff x * exceptional2.coeff (70 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (70 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_70 :
    recurrence2ExceptionalProduct.coeff 70 =
      -((30327408320013 * 10 ^ 70 +
        7669559041567317947571617736571440044513900587346739568970162132023240) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 71 = 67 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_70_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_71_prefix_zero :
    (∑ x ∈ Finset.range 68,
      recurrence2A6Square.coeff x * exceptional2.coeff (71 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (71 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_71 :
    recurrence2ExceptionalProduct.coeff 71 =
      ((157323172588982 * 10 ^ 70 +
        9252969992147064188139553527258744016368397234806206416470511745765934) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 72 = 68 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_71_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_72_prefix_zero :
    (∑ x ∈ Finset.range 69,
      recurrence2A6Square.coeff x * exceptional2.coeff (72 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (72 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_72 :
    recurrence2ExceptionalProduct.coeff 72 =
      ((193270080263200 * 10 ^ 70 +
        6198202700379323559328187728387940966906585045184006454663813955502333) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 73 = 69 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_72_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_73_prefix_zero :
    (∑ x ∈ Finset.range 70,
      recurrence2A6Square.coeff x * exceptional2.coeff (73 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (73 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_73 :
    recurrence2ExceptionalProduct.coeff 73 =
      -((2259668692723739 * 10 ^ 70 +
        4718444193948315736335364659549687561931924518127717836297849039379927) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 74 = 70 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_73_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_74_prefix_zero :
    (∑ x ∈ Finset.range 71,
      recurrence2A6Square.coeff x * exceptional2.coeff (74 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (74 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_74 :
    recurrence2ExceptionalProduct.coeff 74 =
      ((840392942215601 * 10 ^ 70 +
        6577423161743830346410726598659221741654912391223079096460304565973257) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 75 = 71 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_74_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_75_prefix_zero :
    (∑ x ∈ Finset.range 72,
      recurrence2A6Square.coeff x * exceptional2.coeff (75 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (75 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_75 :
    recurrence2ExceptionalProduct.coeff 75 =
      ((25370064399230947 * 10 ^ 70 +
        3330275833313560349711513105629239624254062493027080174283338884223569) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 76 = 72 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_75_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_76_prefix_zero :
    (∑ x ∈ Finset.range 73,
      recurrence2A6Square.coeff x * exceptional2.coeff (76 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (76 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_76 :
    recurrence2ExceptionalProduct.coeff 76 =
      -((47980011996121583 * 10 ^ 70 +
        0298260564945560519673997055024133664248167609800205479327328160459844) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 77 = 73 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_76_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_77_prefix_zero :
    (∑ x ∈ Finset.range 74,
      recurrence2A6Square.coeff x * exceptional2.coeff (77 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (77 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_77 :
    recurrence2ExceptionalProduct.coeff 77 =
      -((202395746359578875 * 10 ^ 70 +
        9179196914435098876171061488034811618123216677731420926706155981218686) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 78 = 74 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_77_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_78_prefix_zero :
    (∑ x ∈ Finset.range 75,
      recurrence2A6Square.coeff x * exceptional2.coeff (78 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (78 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_78 :
    recurrence2ExceptionalProduct.coeff 78 =
      ((830590001658700255 * 10 ^ 70 +
        9100472427276531092159565119588187518274719224427218308220057121901259) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 79 = 75 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_78_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_79_prefix_zero :
    (∑ x ∈ Finset.range 76,
      recurrence2A6Square.coeff x * exceptional2.coeff (79 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (79 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_79 :
    recurrence2ExceptionalProduct.coeff 79 =
      ((685193413067536854 * 10 ^ 70 +
        6139651925789359388306964282802996960405462355593986890466154219830731) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 80 = 76 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_79_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_80_prefix_zero :
    (∑ x ∈ Finset.range 77,
      recurrence2A6Square.coeff x * exceptional2.coeff (80 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (80 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_80 :
    recurrence2ExceptionalProduct.coeff 80 =
      -((9286368465706528068 * 10 ^ 70 +
        4026451852587392742206894080705646306336905794833742392229552794549670) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 81 = 77 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_80_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_81_prefix_zero :
    (∑ x ∈ Finset.range 78,
      recurrence2A6Square.coeff x * exceptional2.coeff (81 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (81 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_81 :
    recurrence2ExceptionalProduct.coeff 81 =
      ((9601158995046983099 * 10 ^ 70 +
        4697264770994548492776951611151888705503395545662336064967216839421634) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 82 = 78 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_81_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_82_prefix_zero :
    (∑ x ∈ Finset.range 79,
      recurrence2A6Square.coeff x * exceptional2.coeff (82 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (82 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_82 :
    recurrence2ExceptionalProduct.coeff 82 =
      ((67444811749567923764 * 10 ^ 70 +
        0587248638851226861750562784197992848404736029312906214765946176213822) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 83 = 79 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_82_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_83_prefix_zero :
    (∑ x ∈ Finset.range 80,
      recurrence2A6Square.coeff x * exceptional2.coeff (83 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (83 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_83 :
    recurrence2ExceptionalProduct.coeff 83 =
      -((205783325162616836314 * 10 ^ 70 +
        1454950803020439658915590999315500295665990340450590667206334292385330) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 84 = 80 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_83_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_84_prefix_zero :
    (∑ x ∈ Finset.range 81,
      recurrence2A6Square.coeff x * exceptional2.coeff (84 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (84 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_84 :
    recurrence2ExceptionalProduct.coeff 84 =
      -((191017000854084115244 * 10 ^ 70 +
        0586378344708196969262620439116297479372467804499339254779396370441013) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 85 = 81 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_84_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_85_prefix_zero :
    (∑ x ∈ Finset.range 82,
      recurrence2A6Square.coeff x * exceptional2.coeff (85 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (85 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_85 :
    recurrence2ExceptionalProduct.coeff 85 =
      ((2031542412801216466541 * 10 ^ 70 +
        7091257381707392331725173363284761996853554531127623746608145845335653) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 86 = 82 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_85_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_86_prefix_zero :
    (∑ x ∈ Finset.range 83,
      recurrence2A6Square.coeff x * exceptional2.coeff (86 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (86 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_86 :
    recurrence2ExceptionalProduct.coeff 86 =
      -((2370279134212870509754 * 10 ^ 70 +
        0304673144216675916109305840796385955298040894575876421375493758655581) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 87 = 83 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_86_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_87_prefix_zero :
    (∑ x ∈ Finset.range 84,
      recurrence2A6Square.coeff x * exceptional2.coeff (87 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (87 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_87 :
    recurrence2ExceptionalProduct.coeff 87 =
      -((10752005359082615412732 * 10 ^ 70 +
        5090480051555007719287570067341887042751297882568511371441428429732787) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 88 = 84 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_87_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_88_prefix_zero :
    (∑ x ∈ Finset.range 85,
      recurrence2A6Square.coeff x * exceptional2.coeff (88 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (88 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_88 :
    recurrence2ExceptionalProduct.coeff 88 =
      ((38331734290069542152326 * 10 ^ 70 +
        5554162916705593370336100691040411567647556973567592561929435150487564) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 89 = 85 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_88_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_89_prefix_zero :
    (∑ x ∈ Finset.range 86,
      recurrence2A6Square.coeff x * exceptional2.coeff (89 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (89 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_89 :
    recurrence2ExceptionalProduct.coeff 89 =
      -((1015373578082761696328 * 10 ^ 70 +
        6563718456561001821040655229898475580299872587895293384841321226786772) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 90 = 86 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_89_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_90_prefix_zero :
    (∑ x ∈ Finset.range 87,
      recurrence2A6Square.coeff x * exceptional2.coeff (90 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (90 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_90 :
    recurrence2ExceptionalProduct.coeff 90 =
      -((256172754146187871883378 * 10 ^ 70 +
        6487517789630557453223351358491621654749255857890192257392361872444865) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 91 = 87 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_90_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_91_prefix_zero :
    (∑ x ∈ Finset.range 88,
      recurrence2A6Square.coeff x * exceptional2.coeff (91 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (91 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_91 :
    recurrence2ExceptionalProduct.coeff 91 =
      ((529072904335011878690799 * 10 ^ 70 +
        4635872815018766244658466631102818236253538683631489463970032653650459) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 92 = 88 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_91_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_92_prefix_zero :
    (∑ x ∈ Finset.range 89,
      recurrence2A6Square.coeff x * exceptional2.coeff (92 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (92 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_92 :
    recurrence2ExceptionalProduct.coeff 92 =
      ((505845707685901658810681 * 10 ^ 70 +
        3045113526479076919156563465549600295555849772694985231177631367324890) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 93 = 89 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_92_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_93_prefix_zero :
    (∑ x ∈ Finset.range 90,
      recurrence2A6Square.coeff x * exceptional2.coeff (93 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (93 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_93 :
    recurrence2ExceptionalProduct.coeff 93 =
      -((4224655657647773841060621 * 10 ^ 70 +
        0809299923708681836991204786224980765477757413272897589827230673861124) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 94 = 90 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_93_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_94_prefix_zero :
    (∑ x ∈ Finset.range 91,
      recurrence2A6Square.coeff x * exceptional2.coeff (94 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (94 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_94 :
    recurrence2ExceptionalProduct.coeff 94 =
      ((5971380087942685996584306 * 10 ^ 70 +
        3721741822983045174763494208449717874918970899853976863448419827424618) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 95 = 91 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_94_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_95_prefix_zero :
    (∑ x ∈ Finset.range 92,
      recurrence2A6Square.coeff x * exceptional2.coeff (95 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (95 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_95 :
    recurrence2ExceptionalProduct.coeff 95 =
      ((10699552024298593034696463 * 10 ^ 70 +
        5772674179134294371079745427978714895522111391423144808527699686743416) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 96 = 92 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_95_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_96_prefix_zero :
    (∑ x ∈ Finset.range 93,
      recurrence2A6Square.coeff x * exceptional2.coeff (96 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (96 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_96 :
    recurrence2ExceptionalProduct.coeff 96 =
      -((54563494076316265710090235 * 10 ^ 70 +
        0191452118127308193091519331667208492964902443918739500943029193089270) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 97 = 93 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_96_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_97_prefix_zero :
    (∑ x ∈ Finset.range 94,
      recurrence2A6Square.coeff x * exceptional2.coeff (97 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (97 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_97 :
    recurrence2ExceptionalProduct.coeff 97 =
      ((62934707710346302696536417 * 10 ^ 70 +
        0962673406580592719412113216846675704753637467137929006912034435228642) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 98 = 94 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_97_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_98_prefix_zero :
    (∑ x ∈ Finset.range 95,
      recurrence2A6Square.coeff x * exceptional2.coeff (98 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (98 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_98 :
    recurrence2ExceptionalProduct.coeff 98 =
      ((130003993977936857315318005 * 10 ^ 70 +
        1890603328715731319343831537237734356652459750186418072304655513105159) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 99 = 95 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_98_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_99_prefix_zero :
    (∑ x ∈ Finset.range 96,
      recurrence2A6Square.coeff x * exceptional2.coeff (99 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (99 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_99 :
    recurrence2ExceptionalProduct.coeff 99 =
      -((576836305665920391158486525 * 10 ^ 70 +
        3692375653578530366691349215998718413787059641577368546022450050287309) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 100 = 96 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_99_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_100_prefix_zero :
    (∑ x ∈ Finset.range 97,
      recurrence2A6Square.coeff x * exceptional2.coeff (100 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (100 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_100 :
    recurrence2ExceptionalProduct.coeff 100 =
      ((678824976613071408739256364 * 10 ^ 70 +
        1113339717494683596301628124971545410968103596051363846061258228112452) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 101 = 97 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_100_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_101_prefix_zero :
    (∑ x ∈ Finset.range 98,
      recurrence2A6Square.coeff x * exceptional2.coeff (101 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (101 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_101 :
    recurrence2ExceptionalProduct.coeff 101 =
      ((976621856991058723891023768 * 10 ^ 70 +
        5056022363494995685047899728686971425732405000916258875180308856099600) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 102 = 98 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_101_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_102_prefix_zero :
    (∑ x ∈ Finset.range 99,
      recurrence2A6Square.coeff x * exceptional2.coeff (102 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (102 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_102 :
    recurrence2ExceptionalProduct.coeff 102 =
      -((4911368581971145354372931284 * 10 ^ 70 +
        6672317983804157894906802557687388180619337689413441895212994040357900) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 103 = 99 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_102_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_103_prefix_zero :
    (∑ x ∈ Finset.range 100,
      recurrence2A6Square.coeff x * exceptional2.coeff (103 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (103 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_103 :
    recurrence2ExceptionalProduct.coeff 103 =
      ((6995775178806802541280548621 * 10 ^ 70 +
        5731527026779996204198718377396410074997023823438595182116490402223402) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 104 = 100 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_103_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_104_prefix_zero :
    (∑ x ∈ Finset.range 101,
      recurrence2A6Square.coeff x * exceptional2.coeff (104 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (104 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_104 :
    recurrence2ExceptionalProduct.coeff 104 =
      ((2800493956758801408864669895 * 10 ^ 70 +
        6757566121754033735693966513685012201598683680819803338901988111176604) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 105 = 101 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_104_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_105_prefix_zero :
    (∑ x ∈ Finset.range 102,
      recurrence2A6Square.coeff x * exceptional2.coeff (105 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (105 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_105 :
    recurrence2ExceptionalProduct.coeff 105 =
      -((30728232510030144703126315930 * 10 ^ 70 +
        4964362524293432101911441225304393789143694897031182657656336107427128) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 106 = 102 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_105_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_106_prefix_zero :
    (∑ x ∈ Finset.range 103,
      recurrence2A6Square.coeff x * exceptional2.coeff (106 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (106 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_106 :
    recurrence2ExceptionalProduct.coeff 106 =
      ((57833735550200740399953999153 * 10 ^ 70 +
        9366487342853499885006525804231283705720907757183381939882506995029648) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 107 = 103 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_106_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_107_prefix_zero :
    (∑ x ∈ Finset.range 104,
      recurrence2A6Square.coeff x * exceptional2.coeff (107 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (107 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_107 :
    recurrence2ExceptionalProduct.coeff 107 =
      -((28876576746669442390492599349 * 10 ^ 70 +
        9834174608936150498668756518252717197847030929331255608618146007659942) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 108 = 104 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_107_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_108_prefix_zero :
    (∑ x ∈ Finset.range 105,
      recurrence2A6Square.coeff x * exceptional2.coeff (108 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (108 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_108 :
    recurrence2ExceptionalProduct.coeff 108 =
      -((109863641123629577694172109882 * 10 ^ 70 +
        7428392756239192327643488205851663630360165798316865930708023169723234) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 109 = 105 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_108_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_109_prefix_zero :
    (∑ x ∈ Finset.range 106,
      recurrence2A6Square.coeff x * exceptional2.coeff (109 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (109 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_109 :
    recurrence2ExceptionalProduct.coeff 109 =
      ((316379558478709605664608966191 * 10 ^ 70 +
        4519217254503896318730003358438400017531935318193432480849237861440294) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 110 = 106 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_109_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_110_prefix_zero :
    (∑ x ∈ Finset.range 107,
      recurrence2A6Square.coeff x * exceptional2.coeff (110 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (110 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_110 :
    recurrence2ExceptionalProduct.coeff 110 =
      -((380989173469896572241602134875 * 10 ^ 70 +
        0317566986624439326663893736074254755692707258283112379320619260267367) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 111 = 107 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_110_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_111_prefix_zero :
    (∑ x ∈ Finset.range 108,
      recurrence2A6Square.coeff x * exceptional2.coeff (111 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (111 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_111 :
    recurrence2ExceptionalProduct.coeff 111 =
      ((16174048964653152765229984619 * 10 ^ 70 +
        7180470719715866263610123463747209635965744383118594512568449463948113) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 112 = 108 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_111_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_112_prefix_zero :
    (∑ x ∈ Finset.range 109,
      recurrence2A6Square.coeff x * exceptional2.coeff (112 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (112 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_112 :
    recurrence2ExceptionalProduct.coeff 112 =
      ((843286013707195127927314936818 * 10 ^ 70 +
        1161369207297596133666305846676135154785975174546785226194463712593599) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 113 = 109 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_112_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_113_prefix_zero :
    (∑ x ∈ Finset.range 110,
      recurrence2A6Square.coeff x * exceptional2.coeff (113 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (113 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_113 :
    recurrence2ExceptionalProduct.coeff 113 =
      -((1733626915126433598913680866805 * 10 ^ 70 +
        6297691464917825559400215327510834268447014153795041728417094308600745) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 114 = 110 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_113_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_114_prefix_zero :
    (∑ x ∈ Finset.range 111,
      recurrence2A6Square.coeff x * exceptional2.coeff (114 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (114 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_114 :
    recurrence2ExceptionalProduct.coeff 114 =
      ((1738077292844312424215549933002 * 10 ^ 70 +
        1249024919399049004910929939304527731741261147697868997013552604483266) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 115 = 111 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_114_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_115_prefix_zero :
    (∑ x ∈ Finset.range 112,
      recurrence2A6Square.coeff x * exceptional2.coeff (115 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (115 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_115 :
    recurrence2ExceptionalProduct.coeff 115 =
      -((142270709871359333779847079306 * 10 ^ 70 +
        5209264122483438709131537003925634465692136837884345983345229257121586) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 116 = 112 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_115_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_116_prefix_zero :
    (∑ x ∈ Finset.range 113,
      recurrence2A6Square.coeff x * exceptional2.coeff (116 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (116 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_116 :
    recurrence2ExceptionalProduct.coeff 116 =
      -((2706576561497382842179733906781 * 10 ^ 70 +
        2102696494643881658966410431585869140943144960671766499664402056109585) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 117 = 113 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_116_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_117_prefix_zero :
    (∑ x ∈ Finset.range 114,
      recurrence2A6Square.coeff x * exceptional2.coeff (117 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (117 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_117 :
    recurrence2ExceptionalProduct.coeff 117 =
      ((5160756731961429513190740741130 * 10 ^ 70 +
        7836348405953177439538457410684174891984310948907917915493707846424055) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 118 = 114 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_117_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_118_prefix_zero :
    (∑ x ∈ Finset.range 115,
      recurrence2A6Square.coeff x * exceptional2.coeff (118 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (118 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_118 :
    recurrence2ExceptionalProduct.coeff 118 =
      -((5189579961905659078062793099510 * 10 ^ 70 +
        6935878702700252826680022575963969606283791137813180815099912851728505) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 119 = 115 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_118_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_119_prefix_zero :
    (∑ x ∈ Finset.range 116,
      recurrence2A6Square.coeff x * exceptional2.coeff (119 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (119 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_119 :
    recurrence2ExceptionalProduct.coeff 119 =
      ((1984113608307749325751447456120 * 10 ^ 70 +
        0729485844887578818513871795374336764587003564419999975375762957168083) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 120 = 116 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_119_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_120_prefix_zero :
    (∑ x ∈ Finset.range 117,
      recurrence2A6Square.coeff x * exceptional2.coeff (120 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (120 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_120 :
    recurrence2ExceptionalProduct.coeff 120 =
      ((3064290815209133222297287139120 * 10 ^ 70 +
        5961557085290623384412172303246879039895199586810078051240994550347555) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 121 = 117 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_120_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_121_prefix_zero :
    (∑ x ∈ Finset.range 118,
      recurrence2A6Square.coeff x * exceptional2.coeff (121 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (121 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_121 :
    recurrence2ExceptionalProduct.coeff 121 =
      -((7041779910121006310676981999328 * 10 ^ 70 +
        7590680728008037759354033523158006388365603661869223039053388898170111) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 122 = 118 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_121_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_122_prefix_zero :
    (∑ x ∈ Finset.range 119,
      recurrence2A6Square.coeff x * exceptional2.coeff (122 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (122 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_122 :
    recurrence2ExceptionalProduct.coeff 122 =
      ((7511850123853507181287843322720 * 10 ^ 70 +
        1667623857396524438232116327212357518709595487292084581779553310204032) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 123 = 119 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_122_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_123_prefix_zero :
    (∑ x ∈ Finset.range 120,
      recurrence2A6Square.coeff x * exceptional2.coeff (123 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (123 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_123 :
    recurrence2ExceptionalProduct.coeff 123 =
      -((4272571389507279641894866745593 * 10 ^ 70 +
        1692870475774335400943078186266068193381714508152530485823678751033424) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 124 = 120 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_123_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_124_prefix_zero :
    (∑ x ∈ Finset.range 121,
      recurrence2A6Square.coeff x * exceptional2.coeff (124 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (124 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_124 :
    recurrence2ExceptionalProduct.coeff 124 =
      -((564085837046512090947264919251 * 10 ^ 70 +
        3647618535886373832612157825213400174789937671353356992272389230518270) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 125 = 121 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_124_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_125_prefix_zero :
    (∑ x ∈ Finset.range 122,
      recurrence2A6Square.coeff x * exceptional2.coeff (125 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (125 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_125 :
    recurrence2ExceptionalProduct.coeff 125 =
      ((4180581222883930284849420077216 * 10 ^ 70 +
        0050169343081451109294431483702344556895840476477048201014040682636034) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 126 = 122 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_125_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_126_prefix_zero :
    (∑ x ∈ Finset.range 123,
      recurrence2A6Square.coeff x * exceptional2.coeff (126 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (126 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_126 :
    recurrence2ExceptionalProduct.coeff 126 =
      -((4974580684167422340906539685046 * 10 ^ 70 +
        8354404133421838858571351523225747512495558760245211059984875368764815) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 127 = 123 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_126_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_127_prefix_zero :
    (∑ x ∈ Finset.range 124,
      recurrence2A6Square.coeff x * exceptional2.coeff (127 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (127 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_127 :
    recurrence2ExceptionalProduct.coeff 127 =
      ((3321855414342779454141175150753 * 10 ^ 70 +
        9107468857344727057069020320500064077854540554511144140529221667706983) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 128 = 124 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_127_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_128_prefix_zero :
    (∑ x ∈ Finset.range 125,
      recurrence2A6Square.coeff x * exceptional2.coeff (128 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (128 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_128 :
    recurrence2ExceptionalProduct.coeff 128 =
      -((848421989474998023722845592076 * 10 ^ 70 +
        3897430198231368287905824906118449834476435105886659379787825020036245) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 129 = 125 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_128_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_129_prefix_zero :
    (∑ x ∈ Finset.range 126,
      recurrence2A6Square.coeff x * exceptional2.coeff (129 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (129 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_129 :
    recurrence2ExceptionalProduct.coeff 129 =
      -((920505798690292723688115506921 * 10 ^ 70 +
        2113392297194427036983168593391025750061198553623402357432522780398593) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 130 = 126 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_129_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_130_prefix_zero :
    (∑ x ∈ Finset.range 127,
      recurrence2A6Square.coeff x * exceptional2.coeff (130 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (130 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_130 :
    recurrence2ExceptionalProduct.coeff 130 =
      ((1424483285631968080630226880997 * 10 ^ 70 +
        3688177000666685709196615540890243400502011657329807819069011873978368) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 131 = 127 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_130_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_131_prefix_zero :
    (∑ x ∈ Finset.range 128,
      recurrence2A6Square.coeff x * exceptional2.coeff (131 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (131 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_131 :
    recurrence2ExceptionalProduct.coeff 131 =
      -((1016866871202270057456261109336 * 10 ^ 70 +
        6583602100618306396878096604620075833966850455377467006777042671307932) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 132 = 128 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_131_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_132_prefix_zero :
    (∑ x ∈ Finset.range 129,
      recurrence2A6Square.coeff x * exceptional2.coeff (132 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (132 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_132 :
    recurrence2ExceptionalProduct.coeff 132 =
      ((367527133241869987766502073523 * 10 ^ 70 +
        8884515078841182609680771016653071223365048102844477637985044370776871) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 133 = 129 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_132_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_133_prefix_zero :
    (∑ x ∈ Finset.range 130,
      recurrence2A6Square.coeff x * exceptional2.coeff (133 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (133 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_133 :
    recurrence2ExceptionalProduct.coeff 133 =
      ((67518477735773249768283405253 * 10 ^ 70 +
        5535029850990308996305103117429292925995453447833274535682368840781909) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 134 = 130 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_133_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_134_prefix_zero :
    (∑ x ∈ Finset.range 131,
      recurrence2A6Square.coeff x * exceptional2.coeff (134 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (134 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_134 :
    recurrence2ExceptionalProduct.coeff 134 =
      -((195541599314439733220540685812 * 10 ^ 70 +
        0206234314903756274920971802835403799526567110405744218514609504619822) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 135 = 131 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_134_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_135_prefix_zero :
    (∑ x ∈ Finset.range 132,
      recurrence2A6Square.coeff x * exceptional2.coeff (135 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (135 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_135 :
    recurrence2ExceptionalProduct.coeff 135 =
      ((141826360593659238037463673557 * 10 ^ 70 +
        1648232289969695523490775203850257651077764476762693921797664961068350) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 136 = 132 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_135_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_136_prefix_zero :
    (∑ x ∈ Finset.range 133,
      recurrence2A6Square.coeff x * exceptional2.coeff (136 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (136 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_136 :
    recurrence2ExceptionalProduct.coeff 136 =
      -((52772341585217920332752800380 * 10 ^ 70 +
        7556787971747202580724355418202209517287677863510325427237075991516017) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 137 = 133 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_136_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_137_prefix_zero :
    (∑ x ∈ Finset.range 134,
      recurrence2A6Square.coeff x * exceptional2.coeff (137 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (137 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_137 :
    recurrence2ExceptionalProduct.coeff 137 =
      -((266037343648290871540772622 * 10 ^ 70 +
        0109147315842759559677837779272051331667866088405040639168334231149267) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 138 = 134 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_137_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_138_prefix_zero :
    (∑ x ∈ Finset.range 135,
      recurrence2A6Square.coeff x * exceptional2.coeff (138 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (138 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_138 :
    recurrence2ExceptionalProduct.coeff 138 =
      ((13919270524834260068864156592 * 10 ^ 70 +
        3326329015344139034407724953399048083124134865251490039317542185214096) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 139 = 135 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_138_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_139_prefix_zero :
    (∑ x ∈ Finset.range 136,
      recurrence2A6Square.coeff x * exceptional2.coeff (139 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (139 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_139 :
    recurrence2ExceptionalProduct.coeff 139 =
      -((9395292200057097978763697070 * 10 ^ 70 +
        7318765435852128828082629302948036738130663731478707865265834767874186) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 140 = 136 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_139_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_140_prefix_zero :
    (∑ x ∈ Finset.range 137,
      recurrence2A6Square.coeff x * exceptional2.coeff (140 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (140 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_140 :
    recurrence2ExceptionalProduct.coeff 140 =
      ((2995940005411745323109310667 * 10 ^ 70 +
        4464390914671289957055852508631847672540361824310366294422212100320564) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 141 = 137 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_140_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_141_prefix_zero :
    (∑ x ∈ Finset.range 138,
      recurrence2A6Square.coeff x * exceptional2.coeff (141 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (141 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_141 :
    recurrence2ExceptionalProduct.coeff 141 =
      ((61980516299132994629724586 * 10 ^ 70 +
        7963153423677586927863447998884966891239123701657834601884554402251064) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 142 = 138 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_141_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_142_prefix_zero :
    (∑ x ∈ Finset.range 139,
      recurrence2A6Square.coeff x * exceptional2.coeff (142 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (142 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_142 :
    recurrence2ExceptionalProduct.coeff 142 =
      -((584238613196211428049621441 * 10 ^ 70 +
        9529856581268831271794842673663127745653803689286808840223580942887708) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 143 = 139 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_142_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_143_prefix_zero :
    (∑ x ∈ Finset.range 140,
      recurrence2A6Square.coeff x * exceptional2.coeff (143 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (143 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_143 :
    recurrence2ExceptionalProduct.coeff 143 =
      ((304512697019243196962359228 * 10 ^ 70 +
        5675525738636569013135506412304597521149732006591654889771420143587296) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 144 = 140 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_143_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_144_prefix_zero :
    (∑ x ∈ Finset.range 141,
      recurrence2A6Square.coeff x * exceptional2.coeff (144 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (144 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_144 :
    recurrence2ExceptionalProduct.coeff 144 =
      -((64875093933639441736606651 * 10 ^ 70 +
        4750755018667949861417405761345184178385558367656201663553698040417379) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 145 = 141 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_144_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_145_prefix_zero :
    (∑ x ∈ Finset.range 142,
      recurrence2A6Square.coeff x * exceptional2.coeff (145 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (145 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_145 :
    recurrence2ExceptionalProduct.coeff 145 =
      -((11663832816515126202338580 * 10 ^ 70 +
        8099805400655236061947232803801712833012659962103709454833376216717709) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 146 = 142 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_145_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_146_prefix_zero :
    (∑ x ∈ Finset.range 143,
      recurrence2A6Square.coeff x * exceptional2.coeff (146 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (146 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_146 :
    recurrence2ExceptionalProduct.coeff 146 =
      ((13409901212491001941358821 * 10 ^ 70 +
        9770263277878583597154469535741790151439676963850949738145939701871948) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 147 = 143 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_146_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_147_prefix_zero :
    (∑ x ∈ Finset.range 144,
      recurrence2A6Square.coeff x * exceptional2.coeff (147 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (147 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_147 :
    recurrence2ExceptionalProduct.coeff 147 =
      -((4193856341800954797106067 * 10 ^ 70 +
        3338879655595881357492738069061077695542810542923845045339272446264126) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 148 = 144 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_147_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_148_prefix_zero :
    (∑ x ∈ Finset.range 145,
      recurrence2A6Square.coeff x * exceptional2.coeff (148 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (148 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_148 :
    recurrence2ExceptionalProduct.coeff 148 =
      ((200445778642751701401934 * 10 ^ 70 +
        4891562173741188102189459033400658668724361305809345853471079001846868) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 149 = 145 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_148_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_149_prefix_zero :
    (∑ x ∈ Finset.range 146,
      recurrence2A6Square.coeff x * exceptional2.coeff (149 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (149 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_149 :
    recurrence2ExceptionalProduct.coeff 149 =
      ((329865733774190079810623 * 10 ^ 70 +
        9716064942154727540451697881574976309309774707093960632985685203048308) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 150 = 146 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_149_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_150_prefix_zero :
    (∑ x ∈ Finset.range 147,
      recurrence2A6Square.coeff x * exceptional2.coeff (150 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (150 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_150 :
    recurrence2ExceptionalProduct.coeff 150 =
      -((125983674825029627246793 * 10 ^ 70 +
        0746041725928433953264810189767665137163822230723556434124107730178599) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 151 = 147 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_150_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_151_prefix_zero :
    (∑ x ∈ Finset.range 148,
      recurrence2A6Square.coeff x * exceptional2.coeff (151 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (151 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_151 :
    recurrence2ExceptionalProduct.coeff 151 =
      ((12176851322104210864051 * 10 ^ 70 +
        5405850395179194994460969482709210620868577243874929294273795343577343) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 152 = 148 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_151_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_152_prefix_zero :
    (∑ x ∈ Finset.range 149,
      recurrence2A6Square.coeff x * exceptional2.coeff (152 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (152 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_152 :
    recurrence2ExceptionalProduct.coeff 152 =
      ((5594623382471179079893 * 10 ^ 70 +
        4049622635296666282208954002527797384174666340399638758379909902743465) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 153 = 149 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_152_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_153_prefix_zero :
    (∑ x ∈ Finset.range 150,
      recurrence2A6Square.coeff x * exceptional2.coeff (153 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (153 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_153 :
    recurrence2ExceptionalProduct.coeff 153 =
      -((2191237259796771418525 * 10 ^ 70 +
        5233562731340876301406574156330860143159914705726126166671232665526789) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 154 = 150 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_153_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_154_prefix_zero :
    (∑ x ∈ Finset.range 151,
      recurrence2A6Square.coeff x * exceptional2.coeff (154 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (154 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_154 :
    recurrence2ExceptionalProduct.coeff 154 =
      ((174091541242205865791 * 10 ^ 70 +
        8979283769642141318031601835887575774993845349924646383691843988718249) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 155 = 151 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_154_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_155_prefix_zero :
    (∑ x ∈ Finset.range 152,
      recurrence2A6Square.coeff x * exceptional2.coeff (155 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (155 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_155 :
    recurrence2ExceptionalProduct.coeff 155 =
      ((78827814340838560950 * 10 ^ 70 +
        5733906839126339896857863289017856265048401595620788524676757728593859) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 156 = 152 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_155_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_156_prefix_zero :
    (∑ x ∈ Finset.range 153,
      recurrence2A6Square.coeff x * exceptional2.coeff (156 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (156 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_156 :
    recurrence2ExceptionalProduct.coeff 156 =
      -((22413176238144911426 * 10 ^ 70 +
        2458691995150997220199808183873312789732385775982564635331140118964405) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 157 = 153 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_156_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_157_prefix_zero :
    (∑ x ∈ Finset.range 154,
      recurrence2A6Square.coeff x * exceptional2.coeff (157 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (157 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_157 :
    recurrence2ExceptionalProduct.coeff 157 =
      ((244303237049703813 * 10 ^ 70 +
        9245863362786512758211268475342128829193355362218291387781965073178689) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 158 = 154 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_157_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_158_prefix_zero :
    (∑ x ∈ Finset.range 155,
      recurrence2A6Square.coeff x * exceptional2.coeff (158 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (158 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_158 :
    recurrence2ExceptionalProduct.coeff 158 =
      ((807423507372207915 * 10 ^ 70 +
        2907479335757457641735578725513709221894655927027863547681573724517979) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 159 = 155 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_158_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_159_prefix_zero :
    (∑ x ∈ Finset.range 156,
      recurrence2A6Square.coeff x * exceptional2.coeff (159 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (159 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_159 :
    recurrence2ExceptionalProduct.coeff 159 =
      -((101550076557735071 * 10 ^ 70 +
        9152395487390308825178512930352380951907572693348839444886798235844935) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 160 = 156 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_159_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_160_prefix_zero :
    (∑ x ∈ Finset.range 157,
      recurrence2A6Square.coeff x * exceptional2.coeff (160 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (160 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_160 :
    recurrence2ExceptionalProduct.coeff 160 =
      -((14346076337618034 * 10 ^ 70 +
        6674098732072327859864518659762823013284910552965697252937107711341099) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 161 = 157 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_160_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_161_prefix_zero :
    (∑ x ∈ Finset.range 158,
      recurrence2A6Square.coeff x * exceptional2.coeff (161 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (161 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_161 :
    recurrence2ExceptionalProduct.coeff 161 =
      ((3752324455656202 * 10 ^ 70 +
        5175798594695044768598150587341907176978182192784982228342718779128899) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 162 = 158 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_161_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_162_prefix_zero :
    (∑ x ∈ Finset.range 159,
      recurrence2A6Square.coeff x * exceptional2.coeff (162 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (162 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_162 :
    recurrence2ExceptionalProduct.coeff 162 =
      ((124992453700994 * 10 ^ 70 +
        6657773579030250564280879448934379679060797919098106674769060153828386) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 163 = 159 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_162_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_163_prefix_zero :
    (∑ x ∈ Finset.range 160,
      recurrence2A6Square.coeff x * exceptional2.coeff (163 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (163 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_163 :
    recurrence2ExceptionalProduct.coeff 163 =
      -((81379664555039 * 10 ^ 70 +
        1610659506352394603439719381635003253060270772036881756842733129218458) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 164 = 160 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_163_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_164_prefix_zero :
    (∑ x ∈ Finset.range 161,
      recurrence2A6Square.coeff x * exceptional2.coeff (164 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (164 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_164 :
    recurrence2ExceptionalProduct.coeff 164 =
      -((758517740107 * 10 ^ 70 +
        6765362504141612171735583427793198626106245897089305997853617511254904) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 165 = 161 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_164_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_165_prefix_zero :
    (∑ x ∈ Finset.range 162,
      recurrence2A6Square.coeff x * exceptional2.coeff (165 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (165 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_165 :
    recurrence2ExceptionalProduct.coeff 165 =
      ((1273456795690 * 10 ^ 70 +
        1737377524756637192476230842930937292795059254395054559133348587128504) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 166 = 162 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_165_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_166_prefix_zero :
    (∑ x ∈ Finset.range 163,
      recurrence2A6Square.coeff x * exceptional2.coeff (166 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (166 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_166 :
    recurrence2ExceptionalProduct.coeff 166 =
      ((32242915903 * 10 ^ 70 +
        3773408856464037003192480328756593916740602000635413577348720061084669) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 167 = 163 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_166_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_167_prefix_zero :
    (∑ x ∈ Finset.range 164,
      recurrence2A6Square.coeff x * exceptional2.coeff (167 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (167 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_167 :
    recurrence2ExceptionalProduct.coeff 167 =
      -((13833753107 * 10 ^ 70 +
        5904323640383786699767225069062916236928974388226747587610721046793019) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 168 = 164 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_167_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_168_prefix_zero :
    (∑ x ∈ Finset.range 165,
      recurrence2A6Square.coeff x * exceptional2.coeff (168 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (168 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_168 :
    recurrence2ExceptionalProduct.coeff 168 =
      -((1028259689 * 10 ^ 70 +
        5851510642794679897085384085863605054563090242254344903407322670942396) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 169 = 165 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_168_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_169_prefix_zero :
    (∑ x ∈ Finset.range 166,
      recurrence2A6Square.coeff x * exceptional2.coeff (169 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (169 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_169 :
    recurrence2ExceptionalProduct.coeff 169 =
      ((49938169 * 10 ^ 70 +
        0329533994375999445818228543781678848472909042592571002744037783640814) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 170 = 166 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_169_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_170_prefix_zero :
    (∑ x ∈ Finset.range 167,
      recurrence2A6Square.coeff x * exceptional2.coeff (170 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (170 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_170 :
    recurrence2ExceptionalProduct.coeff 170 =
      ((11614895 * 10 ^ 70 +
        2729709647106052947168486237021077547041238692312405372213670710400919) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 171 = 167 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_170_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_171_prefix_zero :
    (∑ x ∈ Finset.range 168,
      recurrence2A6Square.coeff x * exceptional2.coeff (171 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (171 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_171 :
    recurrence2ExceptionalProduct.coeff 171 =
      ((834052 * 10 ^ 70 +
        9858705572159031767672384036154792061054113700847169877636327829596313) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 172 = 168 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_171_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_172_prefix_zero :
    (∑ x ∈ Finset.range 169,
      recurrence2A6Square.coeff x * exceptional2.coeff (172 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (172 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_172 :
    recurrence2ExceptionalProduct.coeff 172 =
      ((35138 * 10 ^ 70 +
        0573958967164954559703550661427196371515804502939580702580099887406751) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 173 = 169 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_172_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_173_prefix_zero :
    (∑ x ∈ Finset.range 170,
      recurrence2A6Square.coeff x * exceptional2.coeff (173 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (173 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_173 :
    recurrence2ExceptionalProduct.coeff 173 =
      ((982 * 10 ^ 70 +
        0476536544450933187859581662630978130593051007236900846592254064577823) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 174 = 170 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_173_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_174_prefix_zero :
    (∑ x ∈ Finset.range 171,
      recurrence2A6Square.coeff x * exceptional2.coeff (174 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (174 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_174 :
    recurrence2ExceptionalProduct.coeff 174 =
      ((19 * 10 ^ 70 +
        0201738507549245857740417831814927945194603816871153360522986840951576) : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 175 = 171 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_174_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_175_prefix_zero :
    (∑ x ∈ Finset.range 172,
      recurrence2A6Square.coeff x * exceptional2.coeff (175 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (175 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_175 :
    recurrence2ExceptionalProduct.coeff 175 =
      (2590334884478045949618454757618757374449021359078660735983310493896292 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 176 = 172 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_175_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_176_prefix_zero :
    (∑ x ∈ Finset.range 173,
      recurrence2A6Square.coeff x * exceptional2.coeff (176 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (176 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_176 :
    recurrence2ExceptionalProduct.coeff 176 =
      (24726789264893570127529264904553469105636610184203191232381603508441 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 177 = 173 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_176_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_177_prefix_zero :
    (∑ x ∈ Finset.range 174,
      recurrence2A6Square.coeff x * exceptional2.coeff (177 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (177 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_177 :
    recurrence2ExceptionalProduct.coeff 177 =
      (161802614570873968609746227325830059579355070554895720291438423699 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 178 = 174 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_177_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_178_prefix_zero :
    (∑ x ∈ Finset.range 175,
      recurrence2A6Square.coeff x * exceptional2.coeff (178 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (178 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_178 :
    recurrence2ExceptionalProduct.coeff 178 =
      (684481757264596808744193918080996431643661293377763617859746328 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 179 = 175 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_178_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_179_prefix_zero :
    (∑ x ∈ Finset.range 176,
      recurrence2A6Square.coeff x * exceptional2.coeff (179 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (179 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_179 :
    recurrence2ExceptionalProduct.coeff 179 =
      (1559114659305173638564267988435542366590388297023471845358766 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 180 = 176 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_179_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_180_prefix_zero :
    (∑ x ∈ Finset.range 177,
      recurrence2A6Square.coeff x * exceptional2.coeff (180 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (180 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_180 :
    recurrence2ExceptionalProduct.coeff 180 =
      (18706287284264735025185938886800570797719454105688711427 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 181 = 177 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_180_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_181_prefix_zero :
    (∑ x ∈ Finset.range 178,
      recurrence2A6Square.coeff x * exceptional2.coeff (181 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (181 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_181 :
    recurrence2ExceptionalProduct.coeff 181 =
      (-10279976870582267855639879074409970767282377203252952703 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 182 = 178 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_181_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_182_prefix_zero :
    (∑ x ∈ Finset.range 179,
      recurrence2A6Square.coeff x * exceptional2.coeff (182 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (182 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_182 :
    recurrence2ExceptionalProduct.coeff 182 =
      (-24816490176589969372083057336547509125912462193664260 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 183 = 179 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_182_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_183_prefix_zero :
    (∑ x ∈ Finset.range 180,
      recurrence2A6Square.coeff x * exceptional2.coeff (183 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (183 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_183 :
    recurrence2ExceptionalProduct.coeff 183 =
      (-12064146606251989635038940038993896494134240839726 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 184 = 180 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_183_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_184_prefix_zero :
    (∑ x ∈ Finset.range 181,
      recurrence2A6Square.coeff x * exceptional2.coeff (184 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (184 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_184 :
    recurrence2ExceptionalProduct.coeff 184 =
      (40246446432363529434470043240204824813598601911 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 185 = 181 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_184_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_185_prefix_zero :
    (∑ x ∈ Finset.range 182,
      recurrence2A6Square.coeff x * exceptional2.coeff (185 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (185 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_185 :
    recurrence2ExceptionalProduct.coeff 185 =
      (72138992442074386338722923695269656113364109 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 186 = 182 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_185_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_186_prefix_zero :
    (∑ x ∈ Finset.range 183,
      recurrence2A6Square.coeff x * exceptional2.coeff (186 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (186 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_186 :
    recurrence2ExceptionalProduct.coeff 186 =
      (46018701789594108135664733430096178815735 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 187 = 183 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_186_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_187_prefix_zero :
    (∑ x ∈ Finset.range 184,
      recurrence2A6Square.coeff x * exceptional2.coeff (187 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (187 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_187 :
    recurrence2ExceptionalProduct.coeff 187 =
      (12452683985295238859848991041189999177 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 188 = 184 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_187_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_188_prefix_zero :
    (∑ x ∈ Finset.range 185,
      recurrence2A6Square.coeff x * exceptional2.coeff (188 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (188 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_188 :
    recurrence2ExceptionalProduct.coeff 188 =
      (1242648732597308443281398765999555 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 189 = 185 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_188_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_189_prefix_zero :
    (∑ x ∈ Finset.range 186,
      recurrence2A6Square.coeff x * exceptional2.coeff (189 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (189 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_189 :
    recurrence2ExceptionalProduct.coeff 189 =
      (43661757379497123762590298513 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 190 = 186 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_189_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_190_prefix_zero :
    (∑ x ∈ Finset.range 187,
      recurrence2A6Square.coeff x * exceptional2.coeff (190 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (190 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_190 :
    recurrence2ExceptionalProduct.coeff 190 =
      (251108966979503023409725 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 191 = 187 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_190_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_191_prefix_zero :
    (∑ x ∈ Finset.range 188,
      recurrence2A6Square.coeff x * exceptional2.coeff (191 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (191 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2ExceptionalProduct_coeff_191_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence2A6Square.coeff (191 + x) *
        exceptional2.coeff (191 - (191 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6Square_coeff_high (191 + x) (by omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_191 :
    recurrence2ExceptionalProduct.coeff 191 =
      (396784196304291633 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 192 = 188 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 3 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_191_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2ExceptionalProduct_coeff_191_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_192_prefix_zero :
    (∑ x ∈ Finset.range 189,
      recurrence2A6Square.coeff x * exceptional2.coeff (192 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (192 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2ExceptionalProduct_coeff_192_suffix_zero :
    (∑ x ∈ Finset.range 2,
      recurrence2A6Square.coeff (191 + x) *
        exceptional2.coeff (192 - (191 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6Square_coeff_high (191 + x) (by omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_192 :
    recurrence2ExceptionalProduct.coeff 192 =
      (1259182849 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 193 = 189 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 2 +
      2 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_192_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2ExceptionalProduct_coeff_192_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2ExceptionalProduct_coeff_193_prefix_zero :
    (∑ x ∈ Finset.range 190,
      recurrence2A6Square.coeff x * exceptional2.coeff (193 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2Exceptional_coeff_high (193 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2ExceptionalProduct_coeff_193_suffix_zero :
    (∑ x ∈ Finset.range 3,
      recurrence2A6Square.coeff (191 + x) *
        exceptional2.coeff (193 - (191 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6Square_coeff_high (191 + x) (by omega)]
  norm_num

theorem recurrence2ExceptionalProduct_coeff_193 :
    recurrence2ExceptionalProduct.coeff 193 =
      (1 : ℚ) := by
  unfold recurrence2ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 194 = 190 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 1 +
      3 by norm_num, Finset.sum_range_add]
  rw [recurrence2ExceptionalProduct_coeff_193_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2ExceptionalProduct_coeff_193_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
