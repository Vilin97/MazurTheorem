/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupA4Square
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupExceptional
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupExceptionalProductPart0Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: ExceptionalProduct coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4A4Square_coeff_0
  recurrence4A4Square_coeff_1
  recurrence4A4Square_coeff_10
  recurrence4A4Square_coeff_100
  recurrence4A4Square_coeff_101
  recurrence4A4Square_coeff_102
  recurrence4A4Square_coeff_103
  recurrence4A4Square_coeff_104
  recurrence4A4Square_coeff_105
  recurrence4A4Square_coeff_106
  recurrence4A4Square_coeff_107
  recurrence4A4Square_coeff_108
  recurrence4A4Square_coeff_109
  recurrence4A4Square_coeff_11
  recurrence4A4Square_coeff_110
  recurrence4A4Square_coeff_111
  recurrence4A4Square_coeff_112
  recurrence4A4Square_coeff_113
  recurrence4A4Square_coeff_114
  recurrence4A4Square_coeff_115
  recurrence4A4Square_coeff_116
  recurrence4A4Square_coeff_117
  recurrence4A4Square_coeff_118
  recurrence4A4Square_coeff_119
  recurrence4A4Square_coeff_12
  recurrence4A4Square_coeff_120
  recurrence4A4Square_coeff_121
  recurrence4A4Square_coeff_122
  recurrence4A4Square_coeff_123
  recurrence4A4Square_coeff_124
  recurrence4A4Square_coeff_125
  recurrence4A4Square_coeff_126
  recurrence4A4Square_coeff_127
  recurrence4A4Square_coeff_128
  recurrence4A4Square_coeff_129
  recurrence4A4Square_coeff_13
  recurrence4A4Square_coeff_130
  recurrence4A4Square_coeff_131
  recurrence4A4Square_coeff_132
  recurrence4A4Square_coeff_133
  recurrence4A4Square_coeff_134
  recurrence4A4Square_coeff_135
  recurrence4A4Square_coeff_136
  recurrence4A4Square_coeff_137
  recurrence4A4Square_coeff_138
  recurrence4A4Square_coeff_139
  recurrence4A4Square_coeff_14
  recurrence4A4Square_coeff_140
  recurrence4A4Square_coeff_141
  recurrence4A4Square_coeff_142
  recurrence4A4Square_coeff_143
  recurrence4A4Square_coeff_144
  recurrence4A4Square_coeff_145
  recurrence4A4Square_coeff_146
  recurrence4A4Square_coeff_147
  recurrence4A4Square_coeff_148
  recurrence4A4Square_coeff_149
  recurrence4A4Square_coeff_15
  recurrence4A4Square_coeff_150
  recurrence4A4Square_coeff_151
  recurrence4A4Square_coeff_152
  recurrence4A4Square_coeff_153
  recurrence4A4Square_coeff_154
  recurrence4A4Square_coeff_155

attribute [local simp]
  recurrence4A4Square_coeff_156
  recurrence4A4Square_coeff_157
  recurrence4A4Square_coeff_158
  recurrence4A4Square_coeff_159
  recurrence4A4Square_coeff_16
  recurrence4A4Square_coeff_160
  recurrence4A4Square_coeff_161
  recurrence4A4Square_coeff_162
  recurrence4A4Square_coeff_163
  recurrence4A4Square_coeff_164
  recurrence4A4Square_coeff_165
  recurrence4A4Square_coeff_166
  recurrence4A4Square_coeff_167
  recurrence4A4Square_coeff_168
  recurrence4A4Square_coeff_169
  recurrence4A4Square_coeff_17
  recurrence4A4Square_coeff_170
  recurrence4A4Square_coeff_171
  recurrence4A4Square_coeff_172
  recurrence4A4Square_coeff_173
  recurrence4A4Square_coeff_174
  recurrence4A4Square_coeff_175
  recurrence4A4Square_coeff_176
  recurrence4A4Square_coeff_177
  recurrence4A4Square_coeff_178
  recurrence4A4Square_coeff_179
  recurrence4A4Square_coeff_18
  recurrence4A4Square_coeff_180
  recurrence4A4Square_coeff_181
  recurrence4A4Square_coeff_182
  recurrence4A4Square_coeff_183
  recurrence4A4Square_coeff_184
  recurrence4A4Square_coeff_185
  recurrence4A4Square_coeff_186
  recurrence4A4Square_coeff_187
  recurrence4A4Square_coeff_188
  recurrence4A4Square_coeff_189
  recurrence4A4Square_coeff_19
  recurrence4A4Square_coeff_190
  recurrence4A4Square_coeff_191
  recurrence4A4Square_coeff_192
  recurrence4A4Square_coeff_193
  recurrence4A4Square_coeff_194
  recurrence4A4Square_coeff_195
  recurrence4A4Square_coeff_196
  recurrence4A4Square_coeff_197
  recurrence4A4Square_coeff_198
  recurrence4A4Square_coeff_199
  recurrence4A4Square_coeff_2
  recurrence4A4Square_coeff_20
  recurrence4A4Square_coeff_200
  recurrence4A4Square_coeff_201
  recurrence4A4Square_coeff_202
  recurrence4A4Square_coeff_203
  recurrence4A4Square_coeff_204
  recurrence4A4Square_coeff_205
  recurrence4A4Square_coeff_206
  recurrence4A4Square_coeff_207
  recurrence4A4Square_coeff_208
  recurrence4A4Square_coeff_209
  recurrence4A4Square_coeff_21
  recurrence4A4Square_coeff_210
  recurrence4A4Square_coeff_211
  recurrence4A4Square_coeff_212

attribute [local simp]
  recurrence4A4Square_coeff_213
  recurrence4A4Square_coeff_214
  recurrence4A4Square_coeff_215
  recurrence4A4Square_coeff_216
  recurrence4A4Square_coeff_217
  recurrence4A4Square_coeff_22
  recurrence4A4Square_coeff_23
  recurrence4A4Square_coeff_24
  recurrence4A4Square_coeff_25
  recurrence4A4Square_coeff_26
  recurrence4A4Square_coeff_27
  recurrence4A4Square_coeff_28
  recurrence4A4Square_coeff_29
  recurrence4A4Square_coeff_3
  recurrence4A4Square_coeff_30
  recurrence4A4Square_coeff_31
  recurrence4A4Square_coeff_32
  recurrence4A4Square_coeff_33
  recurrence4A4Square_coeff_34
  recurrence4A4Square_coeff_35
  recurrence4A4Square_coeff_36
  recurrence4A4Square_coeff_37
  recurrence4A4Square_coeff_38
  recurrence4A4Square_coeff_39
  recurrence4A4Square_coeff_4
  recurrence4A4Square_coeff_40
  recurrence4A4Square_coeff_41
  recurrence4A4Square_coeff_42
  recurrence4A4Square_coeff_43
  recurrence4A4Square_coeff_44
  recurrence4A4Square_coeff_45
  recurrence4A4Square_coeff_46
  recurrence4A4Square_coeff_47
  recurrence4A4Square_coeff_48
  recurrence4A4Square_coeff_49
  recurrence4A4Square_coeff_5
  recurrence4A4Square_coeff_50
  recurrence4A4Square_coeff_51
  recurrence4A4Square_coeff_52
  recurrence4A4Square_coeff_53
  recurrence4A4Square_coeff_54
  recurrence4A4Square_coeff_55
  recurrence4A4Square_coeff_56
  recurrence4A4Square_coeff_57
  recurrence4A4Square_coeff_58
  recurrence4A4Square_coeff_59
  recurrence4A4Square_coeff_6
  recurrence4A4Square_coeff_60
  recurrence4A4Square_coeff_61
  recurrence4A4Square_coeff_62
  recurrence4A4Square_coeff_63
  recurrence4A4Square_coeff_64
  recurrence4A4Square_coeff_65
  recurrence4A4Square_coeff_66
  recurrence4A4Square_coeff_67
  recurrence4A4Square_coeff_68
  recurrence4A4Square_coeff_69
  recurrence4A4Square_coeff_7
  recurrence4A4Square_coeff_70
  recurrence4A4Square_coeff_71
  recurrence4A4Square_coeff_72
  recurrence4A4Square_coeff_73
  recurrence4A4Square_coeff_74
  recurrence4A4Square_coeff_75

attribute [local simp]
  recurrence4A4Square_coeff_76
  recurrence4A4Square_coeff_77
  recurrence4A4Square_coeff_78
  recurrence4A4Square_coeff_79
  recurrence4A4Square_coeff_8
  recurrence4A4Square_coeff_80
  recurrence4A4Square_coeff_81
  recurrence4A4Square_coeff_82
  recurrence4A4Square_coeff_83
  recurrence4A4Square_coeff_84
  recurrence4A4Square_coeff_85
  recurrence4A4Square_coeff_86
  recurrence4A4Square_coeff_87
  recurrence4A4Square_coeff_88
  recurrence4A4Square_coeff_89
  recurrence4A4Square_coeff_9
  recurrence4A4Square_coeff_90
  recurrence4A4Square_coeff_91
  recurrence4A4Square_coeff_92
  recurrence4A4Square_coeff_93
  recurrence4A4Square_coeff_94
  recurrence4A4Square_coeff_95
  recurrence4A4Square_coeff_96
  recurrence4A4Square_coeff_97
  recurrence4A4Square_coeff_98
  recurrence4A4Square_coeff_99
  recurrence4Exceptional_coeff_0
  recurrence4Exceptional_coeff_1
  recurrence4Exceptional_coeff_10
  recurrence4Exceptional_coeff_11
  recurrence4Exceptional_coeff_12
  recurrence4Exceptional_coeff_13
  recurrence4Exceptional_coeff_2
  recurrence4Exceptional_coeff_3
  recurrence4Exceptional_coeff_4
  recurrence4Exceptional_coeff_5
  recurrence4Exceptional_coeff_6
  recurrence4Exceptional_coeff_7
  recurrence4Exceptional_coeff_8
  recurrence4Exceptional_coeff_9

theorem recurrence4ExceptionalProduct_coeff_0 :
    recurrence4ExceptionalProduct.coeff 0 =
      (
        (-148021789696) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 1,
    recurrence4A4Square.coeff x * exceptional4.coeff (0 - x)) = _
  rw [show 1 = 0 +
    1 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 1 = 1 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

theorem recurrence4ExceptionalProduct_coeff_1 :
    recurrence4ExceptionalProduct.coeff 1 =
      (
        (425029902975744) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 2,
    recurrence4A4Square.coeff x * exceptional4.coeff (1 - x)) = _
  rw [show 2 = 0 +
    2 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 2 = 2 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

theorem recurrence4ExceptionalProduct_coeff_2 :
    recurrence4ExceptionalProduct.coeff 2 =
      (
        (361363908594464624) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 3,
    recurrence4A4Square.coeff x * exceptional4.coeff (2 - x)) = _
  rw [show 3 = 0 +
    3 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

theorem recurrence4ExceptionalProduct_coeff_3 :
    recurrence4ExceptionalProduct.coeff 3 =
      (
        (-1710740689980747316160) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 4,
    recurrence4A4Square.coeff x * exceptional4.coeff (3 - x)) = _
  rw [show 4 = 0 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

theorem recurrence4ExceptionalProduct_coeff_4 :
    recurrence4ExceptionalProduct.coeff 4 =
      (
        (33321634268823841799180) /
        (1785787687194522429613 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 5,
    recurrence4A4Square.coeff x * exceptional4.coeff (4 - x)) = _
  rw [show 5 = 0 +
    5 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 5 = 5 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

theorem recurrence4ExceptionalProduct_coeff_5 :
    recurrence4ExceptionalProduct.coeff 5 =
      (
        (1568684170453573062994623780) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 6,
    recurrence4A4Square.coeff x * exceptional4.coeff (5 - x)) = _
  rw [show 6 = 0 +
    6 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 6 = 6 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

theorem recurrence4ExceptionalProduct_coeff_6 :
    recurrence4ExceptionalProduct.coeff 6 =
      (
        (-1212801867594562315008195780936) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 7,
    recurrence4A4Square.coeff x * exceptional4.coeff (6 - x)) = _
  rw [show 7 = 0 +
    7 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

theorem recurrence4ExceptionalProduct_coeff_7 :
    recurrence4ExceptionalProduct.coeff 7 =
      (
        (222090859349556932123007586448524) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 8,
    recurrence4A4Square.coeff x * exceptional4.coeff (7 - x)) = _
  rw [show 8 = 0 +
    8 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 8 = 8 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

theorem recurrence4ExceptionalProduct_coeff_8 :
    recurrence4ExceptionalProduct.coeff 8 =
      (
        (29576650571031224960847659738892371) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 9,
    recurrence4A4Square.coeff x * exceptional4.coeff (8 - x)) = _
  rw [show 9 = 0 +
    9 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 9 = 9 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

theorem recurrence4ExceptionalProduct_coeff_9 :
    recurrence4ExceptionalProduct.coeff 9 =
      (
        (-9376111723218189450314480137833538103) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 10,
    recurrence4A4Square.coeff x * exceptional4.coeff (9 - x)) = _
  rw [show 10 = 0 +
    10 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 10 = 10 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

theorem recurrence4ExceptionalProduct_coeff_10 :
    recurrence4ExceptionalProduct.coeff 10 =
      (
        (-1324064904771674529390664983163648610812) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 11,
    recurrence4A4Square.coeff x * exceptional4.coeff (10 - x)) = _
  rw [show 11 = 0 +
    11 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 11 = 11 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

theorem recurrence4ExceptionalProduct_coeff_11 :
    recurrence4ExceptionalProduct.coeff 11 =
      (
        (840726262835178425904176020051287193471402) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 12,
    recurrence4A4Square.coeff x * exceptional4.coeff (11 - x)) = _
  rw [show 12 = 0 +
    12 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 12 = 12 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

theorem recurrence4ExceptionalProduct_coeff_12 :
    recurrence4ExceptionalProduct.coeff 12 =
      (
        (-228594728554308501065228306142824529356454184) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 13,
    recurrence4A4Square.coeff x * exceptional4.coeff (12 - x)) = _
  rw [show 13 = 0 +
    13 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

theorem recurrence4ExceptionalProduct_coeff_13 :
    recurrence4ExceptionalProduct.coeff 13 =
      (
        (51563070341198515455770316143830671198904310754) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 14,
    recurrence4A4Square.coeff x * exceptional4.coeff (13 - x)) = _
  rw [show 14 = 0 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_14_prefix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4A4Square.coeff x * exceptional4.coeff (14 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (14 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_14 :
    recurrence4ExceptionalProduct.coeff 14 =
      (
        (-9156969475137893698375804475381456105113956397943) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 15,
    recurrence4A4Square.coeff x * exceptional4.coeff (14 - x)) = _
  rw [show 15 = 1 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_14_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_15_prefix_zero :
    (∑ x ∈ Finset.range 2,
      recurrence4A4Square.coeff x * exceptional4.coeff (15 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (15 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_15 :
    recurrence4ExceptionalProduct.coeff 15 =
      (
        (1305589300519121038515811130765872536785458407869721) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 16,
    recurrence4A4Square.coeff x * exceptional4.coeff (15 - x)) = _
  rw [show 16 = 2 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_15_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_16_prefix_zero :
    (∑ x ∈ Finset.range 3,
      recurrence4A4Square.coeff x * exceptional4.coeff (16 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (16 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_16 :
    recurrence4ExceptionalProduct.coeff 16 =
      (
        (-207830625181550919456555034908458379347068535422211801) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 17,
    recurrence4A4Square.coeff x * exceptional4.coeff (16 - x)) = _
  rw [show 17 = 3 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_16_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_17_prefix_zero :
    (∑ x ∈ Finset.range 4,
      recurrence4A4Square.coeff x * exceptional4.coeff (17 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (17 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_17 :
    recurrence4ExceptionalProduct.coeff 17 =
      (
        (54906167012788032194573835549272706195365984723334891307) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 18,
    recurrence4A4Square.coeff x * exceptional4.coeff (17 - x)) = _
  rw [show 18 = 4 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_17_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_18_prefix_zero :
    (∑ x ∈ Finset.range 5,
      recurrence4A4Square.coeff x * exceptional4.coeff (18 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (18 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_18 :
    recurrence4ExceptionalProduct.coeff 18 =
      (
        (-17831644626160314087744891606051486810601634983396113759986) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 19,
    recurrence4A4Square.coeff x * exceptional4.coeff (18 - x)) = _
  rw [show 19 = 5 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_18_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_19_prefix_zero :
    (∑ x ∈ Finset.range 6,
      recurrence4A4Square.coeff x * exceptional4.coeff (19 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (19 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_19 :
    recurrence4ExceptionalProduct.coeff 19 =
      (
        (5197750894258186595818375748100966211897686983427724483974072) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 20,
    recurrence4A4Square.coeff x * exceptional4.coeff (19 - x)) = _
  rw [show 20 = 6 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_19_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_20_prefix_zero :
    (∑ x ∈ Finset.range 7,
      recurrence4A4Square.coeff x * exceptional4.coeff (20 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (20 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_20 :
    recurrence4ExceptionalProduct.coeff 20 =
      (
        (-1288988348334583498140437774724849846745915532816260045200305063) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 21,
    recurrence4A4Square.coeff x * exceptional4.coeff (20 - x)) = _
  rw [show 21 = 7 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_20_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_21_prefix_zero :
    (∑ x ∈ Finset.range 8,
      recurrence4A4Square.coeff x * exceptional4.coeff (21 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (21 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_21 :
    recurrence4ExceptionalProduct.coeff 21 =
      (
        (21209581350268564960755453637351665391797776122138543798880549937) /
        (1785787687194522429613 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 22,
    recurrence4A4Square.coeff x * exceptional4.coeff (21 - x)) = _
  rw [show 22 = 8 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_21_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_22_prefix_zero :
    (∑ x ∈ Finset.range 9,
      recurrence4A4Square.coeff x * exceptional4.coeff (22 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (22 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_22 :
    recurrence4ExceptionalProduct.coeff 22 =
      (
        (-51787973424327418626002256866889371142799761373743734838178424228344) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 23,
    recurrence4A4Square.coeff x * exceptional4.coeff (22 - x)) = _
  rw [show 23 = 9 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_22_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_23_prefix_zero :
    (∑ x ∈ Finset.range 10,
      recurrence4A4Square.coeff x * exceptional4.coeff (23 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (23 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_23 :
    recurrence4ExceptionalProduct.coeff 23 =
      (
        (8653406264959136465134877056915981849133961896800524317038148920529702) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 24,
    recurrence4A4Square.coeff x * exceptional4.coeff (23 - x)) = _
  rw [show 24 = 10 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_23_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_24_prefix_zero :
    (∑ x ∈ Finset.range 11,
      recurrence4A4Square.coeff x * exceptional4.coeff (24 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (24 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_24 :
    recurrence4ExceptionalProduct.coeff 24 =
      (
        -((129 * 10 ^ 70 +
          8101235487978630655967213859121424136680727681995601407307819178627571)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 25,
    recurrence4A4Square.coeff x * exceptional4.coeff (24 - x)) = _
  rw [show 25 = 11 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_24_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_25_prefix_zero :
    (∑ x ∈ Finset.range 12,
      recurrence4A4Square.coeff x * exceptional4.coeff (25 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (25 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_25 :
    recurrence4ExceptionalProduct.coeff 25 =
      (
        ((17599 * 10 ^ 70 +
          1479808316575612790892523457156954036447756730365415540563959994682441)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 26,
    recurrence4A4Square.coeff x * exceptional4.coeff (25 - x)) = _
  rw [show 26 = 12 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_25_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_26_prefix_zero :
    (∑ x ∈ Finset.range 13,
      recurrence4A4Square.coeff x * exceptional4.coeff (26 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (26 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_26 :
    recurrence4ExceptionalProduct.coeff 26 =
      (
        -((2167761 * 10 ^ 70 +
          2498373956942659199371923070545487748010193543445081073636999952086217)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 27,
    recurrence4A4Square.coeff x * exceptional4.coeff (26 - x)) = _
  rw [show 27 = 13 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_26_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_27_prefix_zero :
    (∑ x ∈ Finset.range 14,
      recurrence4A4Square.coeff x * exceptional4.coeff (27 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (27 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_27 :
    recurrence4ExceptionalProduct.coeff 27 =
      (
        ((243647016 * 10 ^ 70 +
          9037473719736948509291741291755502247982858221555563249372002737293357)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 28,
    recurrence4A4Square.coeff x * exceptional4.coeff (27 - x)) = _
  rw [show 28 = 14 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_27_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_28_prefix_zero :
    (∑ x ∈ Finset.range 15,
      recurrence4A4Square.coeff x * exceptional4.coeff (28 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (28 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_28 :
    recurrence4ExceptionalProduct.coeff 28 =
      (
        -((25082985746 * 10 ^ 70 +
          9984530186876730048285660208869934385841734811819341822747609547533140)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 29,
    recurrence4A4Square.coeff x * exceptional4.coeff (28 - x)) = _
  rw [show 29 = 15 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_28_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_29_prefix_zero :
    (∑ x ∈ Finset.range 16,
      recurrence4A4Square.coeff x * exceptional4.coeff (29 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (29 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_29 :
    recurrence4ExceptionalProduct.coeff 29 =
      (
        ((2373119648425 * 10 ^ 70 +
          1102867778837728735149004582451883388113811437876439435644504357535108)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 30,
    recurrence4A4Square.coeff x * exceptional4.coeff (29 - x)) = _
  rw [show 30 = 16 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_29_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_30_prefix_zero :
    (∑ x ∈ Finset.range 17,
      recurrence4A4Square.coeff x * exceptional4.coeff (30 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (30 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_30 :
    recurrence4ExceptionalProduct.coeff 30 =
      (
        -((206962885226164 * 10 ^ 70 +
          7426260459675647697745574775390323873446765897511402432351315309960208)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 31,
    recurrence4A4Square.coeff x * exceptional4.coeff (30 - x)) = _
  rw [show 31 = 17 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_30_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_31_prefix_zero :
    (∑ x ∈ Finset.range 18,
      recurrence4A4Square.coeff x * exceptional4.coeff (31 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (31 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_31 :
    recurrence4ExceptionalProduct.coeff 31 =
      (
        ((16683652257094703 * 10 ^ 70 +
          1910707712903168380826939970852570858240079063976839132219688065380988)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 32,
    recurrence4A4Square.coeff x * exceptional4.coeff (31 - x)) = _
  rw [show 32 = 18 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_31_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_32_prefix_zero :
    (∑ x ∈ Finset.range 19,
      recurrence4A4Square.coeff x * exceptional4.coeff (32 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (32 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_32 :
    recurrence4ExceptionalProduct.coeff 32 =
      (
        -((1246267356131866222 * 10 ^ 70 +
          3525814284203780835154112404733432069361810286089612784041559581840852)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 33,
    recurrence4A4Square.coeff x * exceptional4.coeff (32 - x)) = _
  rw [show 33 = 19 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_32_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_33_prefix_zero :
    (∑ x ∈ Finset.range 20,
      recurrence4A4Square.coeff x * exceptional4.coeff (33 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (33 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_33 :
    recurrence4ExceptionalProduct.coeff 33 =
      (
        ((86469863583043081985 * 10 ^ 70 +
          7540422631435709973379384903525468597362873389396043735257871175484976)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 34,
    recurrence4A4Square.coeff x * exceptional4.coeff (33 - x)) = _
  rw [show 34 = 20 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_33_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_34_prefix_zero :
    (∑ x ∈ Finset.range 21,
      recurrence4A4Square.coeff x * exceptional4.coeff (34 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (34 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_34 :
    recurrence4ExceptionalProduct.coeff 34 =
      (
        -((5584590074323924672599 * 10 ^ 70 +
          8168694505410869872868980457531750478050679799556224606127778299710151)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 35,
    recurrence4A4Square.coeff x * exceptional4.coeff (34 - x)) = _
  rw [show 35 = 21 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_34_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_35_prefix_zero :
    (∑ x ∈ Finset.range 22,
      recurrence4A4Square.coeff x * exceptional4.coeff (35 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (35 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_35 :
    recurrence4ExceptionalProduct.coeff 35 =
      (
        ((336408223286813466480201 * 10 ^ 70 +
          1576791788013630421600670053605631431132977842039256294105915667900151)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 36,
    recurrence4A4Square.coeff x * exceptional4.coeff (35 - x)) = _
  rw [show 36 = 22 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_35_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_36_prefix_zero :
    (∑ x ∈ Finset.range 23,
      recurrence4A4Square.coeff x * exceptional4.coeff (36 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (36 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_36 :
    recurrence4ExceptionalProduct.coeff 36 =
      (
        -((18936946810685302877259194 * 10 ^ 70 +
          6175375752715656084579319870765006625117875949911152154243531637587153)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 37,
    recurrence4A4Square.coeff x * exceptional4.coeff (36 - x)) = _
  rw [show 37 = 23 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_36_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_37_prefix_zero :
    (∑ x ∈ Finset.range 24,
      recurrence4A4Square.coeff x * exceptional4.coeff (37 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (37 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_37 :
    recurrence4ExceptionalProduct.coeff 37 =
      (
        ((997906919680749079148547390 * 10 ^ 70 +
          4756289596123444465078584893231693958542541682060770926470914215767799)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 38,
    recurrence4A4Square.coeff x * exceptional4.coeff (37 - x)) = _
  rw [show 38 = 24 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_37_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_38_prefix_zero :
    (∑ x ∈ Finset.range 25,
      recurrence4A4Square.coeff x * exceptional4.coeff (38 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (38 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_38 :
    recurrence4ExceptionalProduct.coeff 38 =
      (
        -((49309411849691549030549681077 * 10 ^ 70 +
          1550053180602677088507570988638061823065419441342287368625028863362526)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 39,
    recurrence4A4Square.coeff x * exceptional4.coeff (38 - x)) = _
  rw [show 39 = 25 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_38_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_39_prefix_zero :
    (∑ x ∈ Finset.range 26,
      recurrence4A4Square.coeff x * exceptional4.coeff (39 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (39 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_39 :
    recurrence4ExceptionalProduct.coeff 39 =
      (
        ((2288288652757008593584022548716 * 10 ^ 70 +
          1059549464626933010065310265757990584575765061809655374473525684599732)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 40,
    recurrence4A4Square.coeff x * exceptional4.coeff (39 - x)) = _
  rw [show 40 = 26 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_39_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_40_prefix_zero :
    (∑ x ∈ Finset.range 27,
      recurrence4A4Square.coeff x * exceptional4.coeff (40 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (40 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_40 :
    recurrence4ExceptionalProduct.coeff 40 =
      (
        -((99879529525479671217639828584505 * 10 ^ 70 +
          9085838563259500419321226509155414726177270452778368062108285675417743)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 41,
    recurrence4A4Square.coeff x * exceptional4.coeff (40 - x)) = _
  rw [show 41 = 27 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_40_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_41_prefix_zero :
    (∑ x ∈ Finset.range 28,
      recurrence4A4Square.coeff x * exceptional4.coeff (41 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (41 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_41 :
    recurrence4ExceptionalProduct.coeff 41 =
      (
        ((4106155538235619123956235243261490 * 10 ^ 70 +
          5606066619935440701390156392892013218082240276530426185534341755876689)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 42,
    recurrence4A4Square.coeff x * exceptional4.coeff (41 - x)) = _
  rw [show 42 = 28 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_41_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_42_prefix_zero :
    (∑ x ∈ Finset.range 29,
      recurrence4A4Square.coeff x * exceptional4.coeff (42 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (42 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_42 :
    recurrence4ExceptionalProduct.coeff 42 =
      (
        -((159207557130490391854234796646874302 * 10 ^ 70 +
          4399455555976056800491470406335852654294203304139874938334469359702661)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 43,
    recurrence4A4Square.coeff x * exceptional4.coeff (42 - x)) = _
  rw [show 43 = 29 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_42_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_43_prefix_zero :
    (∑ x ∈ Finset.range 30,
      recurrence4A4Square.coeff x * exceptional4.coeff (43 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (43 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_43 :
    recurrence4ExceptionalProduct.coeff 43 =
      (
        ((5829178108292145702188316874829342832 * 10 ^ 70 +
          0740234791147839386422175839628194131073486525562721536865304863072781)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 44,
    recurrence4A4Square.coeff x * exceptional4.coeff (43 - x)) = _
  rw [show 44 = 30 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_43_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_44_prefix_zero :
    (∑ x ∈ Finset.range 31,
      recurrence4A4Square.coeff x * exceptional4.coeff (44 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (44 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_44 :
    recurrence4ExceptionalProduct.coeff 44 =
      (
        -((201782773886865096039152730073157665478 * 10 ^ 70 +
          6351038791206733994568387853643762136742582415615115519420765951471995)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 45,
    recurrence4A4Square.coeff x * exceptional4.coeff (44 - x)) = _
  rw [show 45 = 31 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_44_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_45_prefix_zero :
    (∑ x ∈ Finset.range 32,
      recurrence4A4Square.coeff x * exceptional4.coeff (45 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (45 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_45 :
    recurrence4ExceptionalProduct.coeff 45 =
      (
        ((6611273684264671576439076182765237668123 * 10 ^ 70 +
          5783593734655787758182069310306620176652645415687898134390843948130499)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 46,
    recurrence4A4Square.coeff x * exceptional4.coeff (45 - x)) = _
  rw [show 46 = 32 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_45_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_46_prefix_zero :
    (∑ x ∈ Finset.range 33,
      recurrence4A4Square.coeff x * exceptional4.coeff (46 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (46 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_46 :
    recurrence4ExceptionalProduct.coeff 46 =
      (
        -((205246838866044275732646627130229503516631 * 10 ^ 70 +
          8192729962938308731668584648928723336534633282797947428453280648803896)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 47,
    recurrence4A4Square.coeff x * exceptional4.coeff (46 - x)) = _
  rw [show 47 = 33 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_46_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_47_prefix_zero :
    (∑ x ∈ Finset.range 34,
      recurrence4A4Square.coeff x * exceptional4.coeff (47 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (47 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_47 :
    recurrence4ExceptionalProduct.coeff 47 =
      (
        ((6043662057829627722275727128399514190095389 * 10 ^ 70 +
          4988225610662712834876824851318112205959760432960221393391430229938420)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 48,
    recurrence4A4Square.coeff x * exceptional4.coeff (47 - x)) = _
  rw [show 48 = 34 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_47_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_48_prefix_zero :
    (∑ x ∈ Finset.range 35,
      recurrence4A4Square.coeff x * exceptional4.coeff (48 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (48 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_48 :
    recurrence4ExceptionalProduct.coeff 48 =
      (
        -((168956676234637383100498122572288379201377868 * 10 ^ 70 +
          8501919305385892072363010236862716065886344331956163562775625581676475)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 49,
    recurrence4A4Square.coeff x * exceptional4.coeff (48 - x)) = _
  rw [show 49 = 35 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_48_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_49_prefix_zero :
    (∑ x ∈ Finset.range 36,
      recurrence4A4Square.coeff x * exceptional4.coeff (49 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (49 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_49 :
    recurrence4ExceptionalProduct.coeff 49 =
      (
        ((4488477905968890406256643520308226070469683246 * 10 ^ 70 +
          5499822379586094398105775323306096260275931449997194210044182597293001)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 50,
    recurrence4A4Square.coeff x * exceptional4.coeff (49 - x)) = _
  rw [show 50 = 36 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_49_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_50_prefix_zero :
    (∑ x ∈ Finset.range 37,
      recurrence4A4Square.coeff x * exceptional4.coeff (50 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (50 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_50 :
    recurrence4ExceptionalProduct.coeff 50 =
      (
        -((113408872441560499311189050936930561766825262407 * 10 ^ 70 +
          8077090693222462811043971397499688803156663229853473780364188727856253)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 51,
    recurrence4A4Square.coeff x * exceptional4.coeff (50 - x)) = _
  rw [show 51 = 37 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_50_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_51_prefix_zero :
    (∑ x ∈ Finset.range 38,
      recurrence4A4Square.coeff x * exceptional4.coeff (51 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (51 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_51 :
    recurrence4ExceptionalProduct.coeff 51 =
      (
        ((2727557697176272936277916123747783558976822935513 * 10 ^ 70 +
          8015896426726145448262312809079492520080200646247264101444627506974239)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 52,
    recurrence4A4Square.coeff x * exceptional4.coeff (51 - x)) = _
  rw [show 52 = 38 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_51_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_52_prefix_zero :
    (∑ x ∈ Finset.range 39,
      recurrence4A4Square.coeff x * exceptional4.coeff (52 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (52 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_52 :
    recurrence4ExceptionalProduct.coeff 52 =
      (
        -((62490507389941172590447640581995456962935257556131 * 10 ^ 70 +
          7941451408307006893871778669557359087758310680197684027447534782707454)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 53,
    recurrence4A4Square.coeff x * exceptional4.coeff (52 - x)) = _
  rw [show 53 = 39 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_52_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_53_prefix_zero :
    (∑ x ∈ Finset.range 40,
      recurrence4A4Square.coeff x * exceptional4.coeff (53 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (53 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_53 :
    recurrence4ExceptionalProduct.coeff 53 =
      (
        ((104987557612612048927522930693269304921481266791010 * 10 ^ 70 +
          1477590562159814445126005122270529067679068447874757573179800335125838)) /
        (1785787687194522429613 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 54,
    recurrence4A4Square.coeff x * exceptional4.coeff (53 - x)) = _
  rw [show 54 = 40 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_53_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_54_prefix_zero :
    (∑ x ∈ Finset.range 41,
      recurrence4A4Square.coeff x * exceptional4.coeff (54 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (54 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_54 :
    recurrence4ExceptionalProduct.coeff 54 =
      (
        -((28436018458653430498673752759265537924435775644024520 * 10 ^ 70 +
          3664220132697112934901685914767551938972721676154466471954817902026871)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 55,
    recurrence4A4Square.coeff x * exceptional4.coeff (54 - x)) = _
  rw [show 55 = 41 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_54_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_55_prefix_zero :
    (∑ x ∈ Finset.range 42,
      recurrence4A4Square.coeff x * exceptional4.coeff (55 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (55 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_55 :
    recurrence4ExceptionalProduct.coeff 55 =
      (
        ((565522221577685854581525846622436648855031588269631033 * 10 ^ 70 +
          2371322078120270619162944028019353713234073464879227769820888888068963)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 56,
    recurrence4A4Square.coeff x * exceptional4.coeff (55 - x)) = _
  rw [show 56 = 42 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_55_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_56_prefix_zero :
    (∑ x ∈ Finset.range 43,
      recurrence4A4Square.coeff x * exceptional4.coeff (56 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (56 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_56 :
    recurrence4ExceptionalProduct.coeff 56 =
      (
        -((10741763377928742536106442835330847881713646496423163146 * 10 ^ 70 +
          8322116929935760294160616716031800934996972038810163973611495010689146)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 57,
    recurrence4A4Square.coeff x * exceptional4.coeff (56 - x)) = _
  rw [show 57 = 43 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_56_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_57_prefix_zero :
    (∑ x ∈ Finset.range 44,
      recurrence4A4Square.coeff x * exceptional4.coeff (57 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (57 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_57 :
    recurrence4ExceptionalProduct.coeff 57 =
      (
        ((14997990660715920173107855206704664328497373748597657113 * 10 ^ 70 +
          8949648428054977831483899546847735428899590276993839924289387125956014)) /
        (1785787687194522429613 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 58,
    recurrence4A4Square.coeff x * exceptional4.coeff (57 - x)) = _
  rw [show 58 = 44 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_57_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_58_prefix_zero :
    (∑ x ∈ Finset.range 45,
      recurrence4A4Square.coeff x * exceptional4.coeff (58 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (58 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_58 :
    recurrence4ExceptionalProduct.coeff 58 =
      (
        -((3383446257650609433712698072872103210910800210173021046225 * 10 ^ 70 +
          0413630643301792731664321334363098055109735119848197665768071728977599)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 59,
    recurrence4A4Square.coeff x * exceptional4.coeff (58 - x)) = _
  rw [show 59 = 45 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_58_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_59_prefix_zero :
    (∑ x ∈ Finset.range 46,
      recurrence4A4Square.coeff x * exceptional4.coeff (59 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (59 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_59 :
    recurrence4ExceptionalProduct.coeff 59 =
      (
        ((56157385514167856424300304112241199600479942239346289944337 * 10 ^ 70 +
          9049786243958755631778736022690092178309062704644109120506996735636595)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 60,
    recurrence4A4Square.coeff x * exceptional4.coeff (59 - x)) = _
  rw [show 60 = 46 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_59_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_60_prefix_zero :
    (∑ x ∈ Finset.range 47,
      recurrence4A4Square.coeff x * exceptional4.coeff (60 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (60 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_60 :
    recurrence4ExceptionalProduct.coeff 60 =
      (
        -((891816932816022454071208495521588863043832219596816207872541 * 10 ^ 70 +
          6690854174937619338794539558067481528579410421408495925240662922670993)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 61,
    recurrence4A4Square.coeff x * exceptional4.coeff (60 - x)) = _
  rw [show 61 = 47 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_60_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_61_prefix_zero :
    (∑ x ∈ Finset.range 48,
      recurrence4A4Square.coeff x * exceptional4.coeff (61 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (61 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_61 :
    recurrence4ExceptionalProduct.coeff 61 =
      (
        ((13554810512106460748542852997185810758013186380864645414226989 * 10 ^ 70 +
          1407807621901794471125109867208726579070107180771136815323692985282207)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 62,
    recurrence4A4Square.coeff x * exceptional4.coeff (61 - x)) = _
  rw [show 62 = 48 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_61_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_62_prefix_zero :
    (∑ x ∈ Finset.range 49,
      recurrence4A4Square.coeff x * exceptional4.coeff (62 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (62 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_62 :
    recurrence4ExceptionalProduct.coeff 62 =
      (
        -((197222091319506959658867085845268842041720945290669074612356261 * 10 ^ 70 +
          8626098459562017370705835961700036156957742195017365188345476994174734)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 63,
    recurrence4A4Square.coeff x * exceptional4.coeff (62 - x)) = _
  rw [show 63 = 49 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_62_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_63_prefix_zero :
    (∑ x ∈ Finset.range 50,
      recurrence4A4Square.coeff x * exceptional4.coeff (63 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (63 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_63 :
    recurrence4ExceptionalProduct.coeff 63 =
      (
        ((2747393489747568162603919789713816046397105439099807869955956634 * 10 ^ 70 +
          1806378245851502046522943225946763908575639571318311236823074604636232)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 64,
    recurrence4A4Square.coeff x * exceptional4.coeff (63 - x)) = _
  rw [show 64 = 50 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_63_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_64_prefix_zero :
    (∑ x ∈ Finset.range 51,
      recurrence4A4Square.coeff x * exceptional4.coeff (64 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (64 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_64 :
    recurrence4ExceptionalProduct.coeff 64 =
      (
        -((36644234937967442758659068973247267080855356076083406186917114465 * 10 ^ 70 +
          2432389191014537030154065753273527930292294214905154189654281748899652)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 65,
    recurrence4A4Square.coeff x * exceptional4.coeff (64 - x)) = _
  rw [show 65 = 51 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_64_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_65_prefix_zero :
    (∑ x ∈ Finset.range 52,
      recurrence4A4Square.coeff x * exceptional4.coeff (65 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (65 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_65 :
    recurrence4ExceptionalProduct.coeff 65 =
      (
        ((467924555674833388195849786085742873109647420723555624481309247897 * 10 ^ 70 +
          5371987291696657357837918655747539695984364784670150421269333789092862)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 66,
    recurrence4A4Square.coeff x * exceptional4.coeff (65 - x)) = _
  rw [show 66 = 52 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_65_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_66_prefix_zero :
    (∑ x ∈ Finset.range 53,
      recurrence4A4Square.coeff x * exceptional4.coeff (66 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (66 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_66 :
    recurrence4ExceptionalProduct.coeff 66 =
      (
        -((5719212646779211876015452924502660880802652306653297711904051830690 * 10 ^ 70 +
          9604905035539922328757549803086655126934021906110877630729896584720339)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 67,
    recurrence4A4Square.coeff x * exceptional4.coeff (66 - x)) = _
  rw [show 67 = 53 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_66_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_67_prefix_zero :
    (∑ x ∈ Finset.range 54,
      recurrence4A4Square.coeff x * exceptional4.coeff (67 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (67 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_67 :
    recurrence4ExceptionalProduct.coeff 67 =
      (
        ((395757647596594235229126193562288267709990595084543777087855544947 * 10 ^ 70 +
          6375585162108455307080461508266007603298277173475797696454587540458427)) /
        (137368283630347879201 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 68,
    recurrence4A4Square.coeff x * exceptional4.coeff (67 - x)) = _
  rw [show 68 = 54 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_67_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_68_prefix_zero :
    (∑ x ∈ Finset.range 55,
      recurrence4A4Square.coeff x * exceptional4.coeff (68 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (68 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_68 :
    recurrence4ExceptionalProduct.coeff 68 =
      (
        -((57531361118452759062644173843266489044763413679066612510561925220482 * 10 ^ 70 +
          4007784550703755899102061002471370215440695952757679522190019024984230)) /
        (1785787687194522429613 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 69,
    recurrence4A4Square.coeff x * exceptional4.coeff (68 - x)) = _
  rw [show 69 = 55 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_68_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_69_prefix_zero :
    (∑ x ∈ Finset.range 56,
      recurrence4A4Square.coeff x * exceptional4.coeff (69 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (69 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_69 :
    recurrence4ExceptionalProduct.coeff 69 =
      (
        ((7989858153037544939727035173999782630772862310075522306430620085283525 * 10 ^ 70 +
          0541151900147729270776327579586198234469654938962027346513259778112986)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 70,
    recurrence4A4Square.coeff x * exceptional4.coeff (69 - x)) = _
  rw [show 70 = 56 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_69_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_70_prefix_zero :
    (∑ x ∈ Finset.range 57,
      recurrence4A4Square.coeff x * exceptional4.coeff (70 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (70 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_70 :
    recurrence4ExceptionalProduct.coeff 70 =
      (
        -((6264448192790128710093319417587375100106196562533007297822806697636168 * 10 ^ 70 +
          7755492530635624293615673840662601526023622559148972419026532760849810)) /
        (1785787687194522429613 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 71,
    recurrence4A4Square.coeff x * exceptional4.coeff (70 - x)) = _
  rw [show 71 = 57 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_70_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_71_prefix_zero :
    (∑ x ∈ Finset.range 58,
      recurrence4A4Square.coeff x * exceptional4.coeff (71 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (71 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_71 :
    recurrence4ExceptionalProduct.coeff 71 =
      (
        (((79 * 10 ^ 70 +
          0512491232939504756787011988407572404085012510637597782060171650238168) * 10 ^ 70 +
          5024249703080446500748856751359659832354391915105558593379384669847938)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 72,
    recurrence4A4Square.coeff x * exceptional4.coeff (71 - x)) = _
  rw [show 72 = 58 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_71_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_72_prefix_zero :
    (∑ x ∈ Finset.range 59,
      recurrence4A4Square.coeff x * exceptional4.coeff (72 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (72 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_72 :
    recurrence4ExceptionalProduct.coeff 72 =
      (
        -(((728 * 10 ^ 70 +
          8533196613658945431025482924013695217820144643665840841228914951836540) * 10 ^ 70 +
          9837894696784843057607684106520800370562487005493363822177518407573017)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 73,
    recurrence4A4Square.coeff x * exceptional4.coeff (72 - x)) = _
  rw [show 73 = 59 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_72_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_73_prefix_zero :
    (∑ x ∈ Finset.range 60,
      recurrence4A4Square.coeff x * exceptional4.coeff (73 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (73 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_73 :
    recurrence4ExceptionalProduct.coeff 73 =
      (
        (((6358 * 10 ^ 70 +
          3428893024910351594726721076008275717213553796772664804235306685012140) * 10 ^ 70 +
          0523129848657875579473687207635591115458136293813904114608285983761685)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 74,
    recurrence4A4Square.coeff x * exceptional4.coeff (73 - x)) = _
  rw [show 74 = 60 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_73_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_74_prefix_zero :
    (∑ x ∈ Finset.range 61,
      recurrence4A4Square.coeff x * exceptional4.coeff (74 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (74 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_74 :
    recurrence4ExceptionalProduct.coeff 74 =
      (
        -(((4013 * 10 ^ 70 +
          6328935772580052375151810870198032370454054368526567331386498491334985) * 10 ^ 70 +
          7022030770359073161192503673764914455358474467559788241878835155666825)) /
        (1785787687194522429613 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 75,
    recurrence4A4Square.coeff x * exceptional4.coeff (74 - x)) = _
  rw [show 75 = 61 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_74_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_75_prefix_zero :
    (∑ x ∈ Finset.range 62,
      recurrence4A4Square.coeff x * exceptional4.coeff (75 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (75 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_75 :
    recurrence4ExceptionalProduct.coeff 75 =
      (
        (((399016 * 10 ^ 70 +
          6602204185773985775190045552987919781520205558168974362589738957175516) * 10 ^ 70 +
          9324027145470891906022654212929406565821881394842688747665924811226339)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 76,
    recurrence4A4Square.coeff x * exceptional4.coeff (75 - x)) = _
  rw [show 76 = 62 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_75_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_76_prefix_zero :
    (∑ x ∈ Finset.range 63,
      recurrence4A4Square.coeff x * exceptional4.coeff (76 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (76 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_76 :
    recurrence4ExceptionalProduct.coeff 76 =
      (
        -(((2797862 * 10 ^ 70 +
          9487696739648772345931363311278056226362636983811886558047516991089494) * 10 ^ 70 +
          8289014634601198032962981150534795800272773399064049048445828095888676)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 77,
    recurrence4A4Square.coeff x * exceptional4.coeff (76 - x)) = _
  rw [show 77 = 63 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_76_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_77_prefix_zero :
    (∑ x ∈ Finset.range 64,
      recurrence4A4Square.coeff x * exceptional4.coeff (77 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (77 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_77 :
    recurrence4ExceptionalProduct.coeff 77 =
      (
        (((17420997 * 10 ^ 70 +
          7535046820443791990824165305356056543241384595942356682759042413563773) * 10 ^ 70 +
          2070069543619105455459007316287599119325167353777150959828142004785542)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 78,
    recurrence4A4Square.coeff x * exceptional4.coeff (77 - x)) = _
  rw [show 78 = 64 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_77_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_78_prefix_zero :
    (∑ x ∈ Finset.range 65,
      recurrence4A4Square.coeff x * exceptional4.coeff (78 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (78 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_78 :
    recurrence4ExceptionalProduct.coeff 78 =
      (
        -(((88994657 * 10 ^ 70 +
          5847232362766862368970287967896927947925171465381586265102356823975314) * 10 ^ 70 +
          3950354003300817472734811607301479858913079369843479804512590792842316)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 79,
    recurrence4A4Square.coeff x * exceptional4.coeff (78 - x)) = _
  rw [show 79 = 65 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_78_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_79_prefix_zero :
    (∑ x ∈ Finset.range 66,
      recurrence4A4Square.coeff x * exceptional4.coeff (79 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (79 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_79 :
    recurrence4ExceptionalProduct.coeff 79 =
      (
        (((269407309 * 10 ^ 70 +
          6693097450185327528474172167087867738769225597819507787781090079025994) * 10 ^ 70 +
          1302457537027742105730568212575393691585024857745835894211190462000026)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 80,
    recurrence4A4Square.coeff x * exceptional4.coeff (79 - x)) = _
  rw [show 80 = 66 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_79_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_80_prefix_zero :
    (∑ x ∈ Finset.range 67,
      recurrence4A4Square.coeff x * exceptional4.coeff (80 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (80 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_80 :
    recurrence4ExceptionalProduct.coeff 80 =
      (
        (((1271876880 * 10 ^ 70 +
          0651936202344774602673347539241821326282389043794081680998353607849743) * 10 ^ 70 +
          9809013545658450555097560372323040920080250164582599031483730428103868)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 81,
    recurrence4A4Square.coeff x * exceptional4.coeff (80 - x)) = _
  rw [show 81 = 67 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_80_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_81_prefix_zero :
    (∑ x ∈ Finset.range 68,
      recurrence4A4Square.coeff x * exceptional4.coeff (81 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (81 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_81 :
    recurrence4ExceptionalProduct.coeff 81 =
      (
        -(((33378787807 * 10 ^ 70 +
          0076389279525776243340872815835773040159524691795770898447491071801187) * 10 ^ 70 +
          8674019615114746405521778525067265713126145457453930167268919585697220)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 82,
    recurrence4A4Square.coeff x * exceptional4.coeff (81 - x)) = _
  rw [show 82 = 68 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_81_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_82_prefix_zero :
    (∑ x ∈ Finset.range 69,
      recurrence4A4Square.coeff x * exceptional4.coeff (82 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (82 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_82 :
    recurrence4ExceptionalProduct.coeff 82 =
      (
        (((398507124438 * 10 ^ 70 +
          3747383671599318215923468953790214804983771841146015434914581829632340) * 10 ^ 70 +
          5328529484830063421237618878948796337819453300689212608910900805695766)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 83,
    recurrence4A4Square.coeff x * exceptional4.coeff (82 - x)) = _
  rw [show 83 = 69 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_82_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_83_prefix_zero :
    (∑ x ∈ Finset.range 70,
      recurrence4A4Square.coeff x * exceptional4.coeff (83 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (83 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_83 :
    recurrence4ExceptionalProduct.coeff 83 =
      (
        -(((3720145493743 * 10 ^ 70 +
          8956724354986301452524504075833448988893831322876850124708804303901300) * 10 ^ 70 +
          8866584866448305882852998855403005620571825964626585536294117463766468)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 84,
    recurrence4A4Square.coeff x * exceptional4.coeff (83 - x)) = _
  rw [show 84 = 70 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_83_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_84_prefix_zero :
    (∑ x ∈ Finset.range 71,
      recurrence4A4Square.coeff x * exceptional4.coeff (84 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (84 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_84 :
    recurrence4ExceptionalProduct.coeff 84 =
      (
        (((29875693698891 * 10 ^ 70 +
          5303425230867934557352857367381063641278601778320598864803422793247580) * 10 ^ 70 +
          1623754232478279203897820283918616372215111962296635580063136622292334)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 85,
    recurrence4A4Square.coeff x * exceptional4.coeff (84 - x)) = _
  rw [show 85 = 71 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_84_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_85_prefix_zero :
    (∑ x ∈ Finset.range 72,
      recurrence4A4Square.coeff x * exceptional4.coeff (85 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (85 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_85 :
    recurrence4ExceptionalProduct.coeff 85 =
      (
        -(((212047387042974 * 10 ^ 70 +
          5192449968284957013212933843344560810255529133477032470382022744861174) * 10 ^ 70 +
          5218962669707237388573615381776848784919884458495330173713401698017606)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 86,
    recurrence4A4Square.coeff x * exceptional4.coeff (85 - x)) = _
  rw [show 86 = 72 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_85_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_86_prefix_zero :
    (∑ x ∈ Finset.range 73,
      recurrence4A4Square.coeff x * exceptional4.coeff (86 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (86 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_86 :
    recurrence4ExceptionalProduct.coeff 86 =
      (
        (((1328469974686458 * 10 ^ 70 +
          6867494407156835511030385048275357395789739895386685438570434570824063) * 10 ^ 70 +
          7861915746580600466467778204861644246054216082577076563627910836535864)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 87,
    recurrence4A4Square.coeff x * exceptional4.coeff (86 - x)) = _
  rw [show 87 = 73 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_86_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_87_prefix_zero :
    (∑ x ∈ Finset.range 74,
      recurrence4A4Square.coeff x * exceptional4.coeff (87 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (87 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_87 :
    recurrence4ExceptionalProduct.coeff 87 =
      (
        -(((7126058882803933 * 10 ^ 70 +
          3474784539726292739862555645682078912131758110475238880023431557176018) * 10 ^ 70 +
          6529725009332972415040798318122567220392765050825705389813552090146864)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 88,
    recurrence4A4Square.coeff x * exceptional4.coeff (87 - x)) = _
  rw [show 88 = 74 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_87_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_88_prefix_zero :
    (∑ x ∈ Finset.range 75,
      recurrence4A4Square.coeff x * exceptional4.coeff (88 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (88 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_88 :
    recurrence4ExceptionalProduct.coeff 88 =
      (
        (((29468186450453120 * 10 ^ 70 +
          4847735949957855166976245484400771561055988887012533759499413366363105) * 10 ^ 70 +
          6933366277668589514580535996513412721568810298993246341356246080200971)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 89,
    recurrence4A4Square.coeff x * exceptional4.coeff (88 - x)) = _
  rw [show 89 = 75 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_88_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_89_prefix_zero :
    (∑ x ∈ Finset.range 76,
      recurrence4A4Square.coeff x * exceptional4.coeff (89 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (89 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_89 :
    recurrence4ExceptionalProduct.coeff 89 =
      (
        -(((49402260296429798 * 10 ^ 70 +
          9097021792146755552380071222874909630007894460902808064348704602941029) * 10 ^ 70 +
          5610391419423653932431587153385926891320025335039550172549418253059461)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 90,
    recurrence4A4Square.coeff x * exceptional4.coeff (89 - x)) = _
  rw [show 90 = 76 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_89_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_90_prefix_zero :
    (∑ x ∈ Finset.range 77,
      recurrence4A4Square.coeff x * exceptional4.coeff (90 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (90 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_90 :
    recurrence4ExceptionalProduct.coeff 90 =
      (
        -(((684493387012791679 * 10 ^ 70 +
          6080109031568197418181485043101667690530506853362972737549761509604371) * 10 ^ 70 +
          8558342683283867008256793950116252982187643542939358123887905122972793)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 91,
    recurrence4A4Square.coeff x * exceptional4.coeff (90 - x)) = _
  rw [show 91 = 77 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_90_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_91_prefix_zero :
    (∑ x ∈ Finset.range 78,
      recurrence4A4Square.coeff x * exceptional4.coeff (91 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (91 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_91 :
    recurrence4ExceptionalProduct.coeff 91 =
      (
        (((10537502264168943847 * 10 ^ 70 +
          1817721447655707971684332182544914684622296569539747597791700473751842) * 10 ^ 70 +
          5341090071092193306075820331347687485211742069166488457248009154114599)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 92,
    recurrence4A4Square.coeff x * exceptional4.coeff (91 - x)) = _
  rw [show 92 = 78 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_91_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_92_prefix_zero :
    (∑ x ∈ Finset.range 79,
      recurrence4A4Square.coeff x * exceptional4.coeff (92 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (92 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_92 :
    recurrence4ExceptionalProduct.coeff 92 =
      (
        -(((99191483647611354618 * 10 ^ 70 +
          6885345484931530385694075870875043332997756863042434078032949078513763) * 10 ^ 70 +
          1756012804680735374090806183076974669209996776100638463412003717147092)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 93,
    recurrence4A4Square.coeff x * exceptional4.coeff (92 - x)) = _
  rw [show 93 = 79 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_92_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_93_prefix_zero :
    (∑ x ∈ Finset.range 80,
      recurrence4A4Square.coeff x * exceptional4.coeff (93 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (93 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_93 :
    recurrence4ExceptionalProduct.coeff 93 =
      (
        (((758154383648326507805 * 10 ^ 70 +
          4793951834815331147633951574813802758557917494623369788896409454425932) * 10 ^ 70 +
          8759423016716322390433267218340727361806205718566622599881339507707760)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 94,
    recurrence4A4Square.coeff x * exceptional4.coeff (93 - x)) = _
  rw [show 94 = 80 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_93_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_94_prefix_zero :
    (∑ x ∈ Finset.range 81,
      recurrence4A4Square.coeff x * exceptional4.coeff (94 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (94 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_94 :
    recurrence4ExceptionalProduct.coeff 94 =
      (
        -(((5022408663954536368860 * 10 ^ 70 +
          8851148708803805335328875168181410179305090041786480268693419606453851) * 10 ^ 70 +
          1778755560114694302212629872340707808191947900265441606003028167362718)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 95,
    recurrence4A4Square.coeff x * exceptional4.coeff (94 - x)) = _
  rw [show 95 = 81 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_94_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_95_prefix_zero :
    (∑ x ∈ Finset.range 82,
      recurrence4A4Square.coeff x * exceptional4.coeff (95 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (95 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_95 :
    recurrence4ExceptionalProduct.coeff 95 =
      (
        (((29277369729918561602525 * 10 ^ 70 +
          3051694477658214192505263825855900108241381508036188934010612761350471) * 10 ^ 70 +
          9158901551576472520260843714480581075202898207432274382105792889695742)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 96,
    recurrence4A4Square.coeff x * exceptional4.coeff (95 - x)) = _
  rw [show 96 = 82 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_95_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_96_prefix_zero :
    (∑ x ∈ Finset.range 83,
      recurrence4A4Square.coeff x * exceptional4.coeff (96 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (96 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_96 :
    recurrence4ExceptionalProduct.coeff 96 =
      (
        -(((148001235833535127875650 * 10 ^ 70 +
          5779874298180301549676396476103650232556482375079829026981838498258482) * 10 ^ 70 +
          5030325393535762339099529514994221330780054923351321748447381918281674)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 97,
    recurrence4A4Square.coeff x * exceptional4.coeff (96 - x)) = _
  rw [show 97 = 83 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_96_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_97_prefix_zero :
    (∑ x ∈ Finset.range 84,
      recurrence4A4Square.coeff x * exceptional4.coeff (97 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (97 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_97 :
    recurrence4ExceptionalProduct.coeff 97 =
      (
        (((608083038114279842993904 * 10 ^ 70 +
          9832326578731127742276421345385479900699635870452453713889792066532804) * 10 ^ 70 +
          7749063417145882988190591634337084235180287192897563948286889991692600)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 98,
    recurrence4A4Square.coeff x * exceptional4.coeff (97 - x)) = _
  rw [show 98 = 84 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_97_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_98_prefix_zero :
    (∑ x ∈ Finset.range 85,
      recurrence4A4Square.coeff x * exceptional4.coeff (98 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (98 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_98 :
    recurrence4ExceptionalProduct.coeff 98 =
      (
        -(((1527434050394492251903417 * 10 ^ 70 +
          5064226464779275205499400381391981590859874524151287035647894556828065) * 10 ^ 70 +
          5367283239520488116992844084449069443780385782466973492203929047631621)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 99,
    recurrence4A4Square.coeff x * exceptional4.coeff (98 - x)) = _
  rw [show 99 = 85 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_98_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_99_prefix_zero :
    (∑ x ∈ Finset.range 86,
      recurrence4A4Square.coeff x * exceptional4.coeff (99 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (99 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_99 :
    recurrence4ExceptionalProduct.coeff 99 =
      (
        -(((4355304152752167678819613 * 10 ^ 70 +
          9785082666662547959869804188666882060627179242436975815542275435296060) * 10 ^ 70 +
          9725726412943322493861132049311984265380033349519345133994232675407353)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 100,
    recurrence4A4Square.coeff x * exceptional4.coeff (99 - x)) = _
  rw [show 100 = 86 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_99_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_100_prefix_zero :
    (∑ x ∈ Finset.range 87,
      recurrence4A4Square.coeff x * exceptional4.coeff (100 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (100 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_100 :
    recurrence4ExceptionalProduct.coeff 100 =
      (
        (((100626325670200678606520333 * 10 ^ 70 +
          7305237151009820302221650244416174424887596459209816974681495643856538) * 10 ^ 70 +
          2306709965242608131288645458654213241634310966050052319428286928609250)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 101,
    recurrence4A4Square.coeff x * exceptional4.coeff (100 - x)) = _
  rw [show 101 = 87 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_100_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_101_prefix_zero :
    (∑ x ∈ Finset.range 88,
      recurrence4A4Square.coeff x * exceptional4.coeff (101 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (101 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_101 :
    recurrence4ExceptionalProduct.coeff 101 =
      (
        -(((73355809063739204257211692 * 10 ^ 70 +
          7687558706473879685537131057884559004189887246572477316746326879296743) * 10 ^ 70 +
          3253020147358971742759541715106238712939958036455643790328237358630864)) /
        (1785787687194522429613 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 102,
    recurrence4A4Square.coeff x * exceptional4.coeff (101 - x)) = _
  rw [show 102 = 88 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_101_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_102_prefix_zero :
    (∑ x ∈ Finset.range 89,
      recurrence4A4Square.coeff x * exceptional4.coeff (102 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (102 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_102 :
    recurrence4ExceptionalProduct.coeff 102 =
      (
        (((7015461190117635319517503856 * 10 ^ 70 +
          4706140865402190540565543822624222060699559820977669819991360967726388) * 10 ^ 70 +
          7420000479557060903269542537096533153146825736235684352608525486970915)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 103,
    recurrence4A4Square.coeff x * exceptional4.coeff (102 - x)) = _
  rw [show 103 = 89 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_102_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_103_prefix_zero :
    (∑ x ∈ Finset.range 90,
      recurrence4A4Square.coeff x * exceptional4.coeff (103 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (103 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_103 :
    recurrence4ExceptionalProduct.coeff 103 =
      (
        -(((44565965390223622171617288457 * 10 ^ 70 +
          4712613171903490990080416233428284323817376841467153732281148015795421) * 10 ^ 70 +
          1739234545835308502167748363674283740104667108991681617070726493524545)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 104,
    recurrence4A4Square.coeff x * exceptional4.coeff (103 - x)) = _
  rw [show 104 = 90 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_103_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_104_prefix_zero :
    (∑ x ∈ Finset.range 91,
      recurrence4A4Square.coeff x * exceptional4.coeff (104 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (104 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_104 :
    recurrence4ExceptionalProduct.coeff 104 =
      (
        (((252837877988187576611606763804 * 10 ^ 70 +
          6555715697552350575254486211612652986267541383795598804061469897348407) * 10 ^ 70 +
          7266256226981196104428907944449194042382170836167059164445398310986656)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 105,
    recurrence4A4Square.coeff x * exceptional4.coeff (104 - x)) = _
  rw [show 105 = 91 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_104_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_105_prefix_zero :
    (∑ x ∈ Finset.range 92,
      recurrence4A4Square.coeff x * exceptional4.coeff (105 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (105 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_105 :
    recurrence4ExceptionalProduct.coeff 105 =
      (
        -(((99298262962671091521627685299 * 10 ^ 70 +
          4646536746639806057869494443730509552822282443645770896088115823709246) * 10 ^ 70 +
          3139732765626424940966835901018411074950042071385729911871891262407082)) /
        (1785787687194522429613 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 106,
    recurrence4A4Square.coeff x * exceptional4.coeff (105 - x)) = _
  rw [show 106 = 92 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_105_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_106_prefix_zero :
    (∑ x ∈ Finset.range 93,
      recurrence4A4Square.coeff x * exceptional4.coeff (106 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (106 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_106 :
    recurrence4ExceptionalProduct.coeff 106 =
      (
        (((5861481024461385705954576658548 * 10 ^ 70 +
          5182548105340714078778551998750718587651535871695229384735671368583120) * 10 ^ 70 +
          8069598649552914522214083825978208804751104567320564581889166922718222)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 107,
    recurrence4A4Square.coeff x * exceptional4.coeff (106 - x)) = _
  rw [show 107 = 93 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_106_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_107_prefix_zero :
    (∑ x ∈ Finset.range 94,
      recurrence4A4Square.coeff x * exceptional4.coeff (107 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (107 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_107 :
    recurrence4ExceptionalProduct.coeff 107 =
      (
        -(((22636177690877328758647502030050 * 10 ^ 70 +
          7450348805817077849855835025468291236515031952431075326426726072648826) * 10 ^ 70 +
          8348322649121167938193845437999252374952357472601078012890572639329940)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 108,
    recurrence4A4Square.coeff x * exceptional4.coeff (107 - x)) = _
  rw [show 108 = 94 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_107_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_108_prefix_zero :
    (∑ x ∈ Finset.range 95,
      recurrence4A4Square.coeff x * exceptional4.coeff (108 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (108 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_108 :
    recurrence4ExceptionalProduct.coeff 108 =
      (
        (((63444731457960731886854248879414 * 10 ^ 70 +
          8924199557936674116397480503046692521365323361361932192350029258813918) * 10 ^ 70 +
          3375182635108542742489161958040970853983451873671344732010035974712105)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 109,
    recurrence4A4Square.coeff x * exceptional4.coeff (108 - x)) = _
  rw [show 109 = 95 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_108_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_109_prefix_zero :
    (∑ x ∈ Finset.range 96,
      recurrence4A4Square.coeff x * exceptional4.coeff (109 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (109 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_109 :
    recurrence4ExceptionalProduct.coeff 109 =
      (
        -(((660775787600255599089159803773 * 10 ^ 70 +
          5677581594448460690856508233900819810458938223128155114344276595037699) * 10 ^ 70 +
          3018838966282595893700986125631296175924404769673830153501584482550165)) /
        (1785787687194522429613 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 110,
    recurrence4A4Square.coeff x * exceptional4.coeff (109 - x)) = _
  rw [show 110 = 96 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_109_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_110_prefix_zero :
    (∑ x ∈ Finset.range 97,
      recurrence4A4Square.coeff x * exceptional4.coeff (110 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (110 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_110 :
    recurrence4ExceptionalProduct.coeff 110 =
      (
        -(((1651413536756646430032508412724208 * 10 ^ 70 +
          8535225556270193831238008387315906465830254420189378390372899370144257) * 10 ^ 70 +
          4166463668258148676849659597789447314562461064550983251650784903458281)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 111,
    recurrence4A4Square.coeff x * exceptional4.coeff (110 - x)) = _
  rw [show 111 = 97 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_110_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_111_prefix_zero :
    (∑ x ∈ Finset.range 98,
      recurrence4A4Square.coeff x * exceptional4.coeff (111 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (111 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_111 :
    recurrence4ExceptionalProduct.coeff 111 =
      (
        (((16663522096213430021733776503652778 * 10 ^ 70 +
          5517842568655569346916166748710290673802495982865074090361082262264368) * 10 ^ 70 +
          3211104672791589417442711204998407529043890583137468733949277018142993)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 112,
    recurrence4A4Square.coeff x * exceptional4.coeff (111 - x)) = _
  rw [show 112 = 98 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_111_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_112_prefix_zero :
    (∑ x ∈ Finset.range 99,
      recurrence4A4Square.coeff x * exceptional4.coeff (112 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (112 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_112 :
    recurrence4ExceptionalProduct.coeff 112 =
      (
        -(((121134296579466495041578391328680678 * 10 ^ 70 +
          3903144950060464751299388638044108534457085809623931619759935381583945) * 10 ^ 70 +
          3708912250716905901873206261808219609472597931548162653117727460157481)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 113,
    recurrence4A4Square.coeff x * exceptional4.coeff (112 - x)) = _
  rw [show 113 = 99 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_112_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_113_prefix_zero :
    (∑ x ∈ Finset.range 100,
      recurrence4A4Square.coeff x * exceptional4.coeff (113 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (113 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_113 :
    recurrence4ExceptionalProduct.coeff 113 =
      (
        (((757955160513769065044571460026052468 * 10 ^ 70 +
          2667523538768543714463901422292197036644307971787518203336740100311419) * 10 ^ 70 +
          2940387707685264642621939465053221654476170511810219036735816945653013)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 114,
    recurrence4A4Square.coeff x * exceptional4.coeff (113 - x)) = _
  rw [show 114 = 100 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_113_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_114_prefix_zero :
    (∑ x ∈ Finset.range 101,
      recurrence4A4Square.coeff x * exceptional4.coeff (114 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (114 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_114 :
    recurrence4ExceptionalProduct.coeff 114 =
      (
        -(((4316071501418032464452462665776044119 * 10 ^ 70 +
          4027061456719661016673071071017102124397285312283026574210517311669033) * 10 ^ 70 +
          8188991977703092957161566617705503168974274758725497327400805037659060)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 115,
    recurrence4A4Square.coeff x * exceptional4.coeff (114 - x)) = _
  rw [show 115 = 101 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_114_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_115_prefix_zero :
    (∑ x ∈ Finset.range 102,
      recurrence4A4Square.coeff x * exceptional4.coeff (115 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (115 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_115 :
    recurrence4ExceptionalProduct.coeff 115 =
      (
        (((22935679790816925063617082583007188004 * 10 ^ 70 +
          8250350187022404591893680301164995567858714333554876792364976865543924) * 10 ^ 70 +
          9859885043523382636925487050237990709943772191339945107969550401300964)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 116,
    recurrence4A4Square.coeff x * exceptional4.coeff (115 - x)) = _
  rw [show 116 = 102 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_115_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_116_prefix_zero :
    (∑ x ∈ Finset.range 103,
      recurrence4A4Square.coeff x * exceptional4.coeff (116 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (116 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_116 :
    recurrence4ExceptionalProduct.coeff 116 =
      (
        -(((115304984354118298212459513732662654643 * 10 ^ 70 +
          7026616267340369274279079883229740460216176436637558524899851669449993) * 10 ^ 70 +
          1774468401492041623929562973349257103196715744276771576994620388952096)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 117,
    recurrence4A4Square.coeff x * exceptional4.coeff (116 - x)) = _
  rw [show 117 = 103 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_116_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_117_prefix_zero :
    (∑ x ∈ Finset.range 104,
      recurrence4A4Square.coeff x * exceptional4.coeff (117 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (117 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_117 :
    recurrence4ExceptionalProduct.coeff 117 =
      (
        (((553008199480065078313602968771622014421 * 10 ^ 70 +
          4571176666938180985373490269896183704973836803596079621261148299306453) * 10 ^ 70 +
          7449105089653374509394554276382293179968980072246732857706075554333296)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 118,
    recurrence4A4Square.coeff x * exceptional4.coeff (117 - x)) = _
  rw [show 118 = 104 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_117_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_118_prefix_zero :
    (∑ x ∈ Finset.range 105,
      recurrence4A4Square.coeff x * exceptional4.coeff (118 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (118 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_118 :
    recurrence4ExceptionalProduct.coeff 118 =
      (
        -(((2544343845600998037343743677301233877114 * 10 ^ 70 +
          6823858561694217936897810823027376233743844013289842525991011817065206) * 10 ^ 70 +
          9860772631114728350967240896648991154941814155615008968462327089818849)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 119,
    recurrence4A4Square.coeff x * exceptional4.coeff (118 - x)) = _
  rw [show 119 = 105 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_118_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_119_prefix_zero :
    (∑ x ∈ Finset.range 106,
      recurrence4A4Square.coeff x * exceptional4.coeff (119 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (119 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_119 :
    recurrence4ExceptionalProduct.coeff 119 =
      (
        (((11274147823585369765312019886510605405188 * 10 ^ 70 +
          1145568795603129240255888870516603127384905440228164639412509481817074) * 10 ^ 70 +
          7747365552537527047866230834450001063346907417479864744484133683488527)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 120,
    recurrence4A4Square.coeff x * exceptional4.coeff (119 - x)) = _
  rw [show 120 = 106 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_119_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_120_prefix_zero :
    (∑ x ∈ Finset.range 107,
      recurrence4A4Square.coeff x * exceptional4.coeff (120 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (120 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_120 :
    recurrence4ExceptionalProduct.coeff 120 =
      (
        -(((48251826016845486517588157432508829859049 * 10 ^ 70 +
          5649212926057827540982351494352764212779848863880851229239871871048564) * 10 ^ 70 +
          3734241205791087407579167426779069873996550257283215973683358820016080)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 121,
    recurrence4A4Square.coeff x * exceptional4.coeff (120 - x)) = _
  rw [show 121 = 107 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_120_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_121_prefix_zero :
    (∑ x ∈ Finset.range 108,
      recurrence4A4Square.coeff x * exceptional4.coeff (121 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (121 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_121 :
    recurrence4ExceptionalProduct.coeff 121 =
      (
        (((199908174017358741103632918918415575302818 * 10 ^ 70 +
          4814469693803189792377597505168012373325632852820206097358843714019942) * 10 ^ 70 +
          0169678765970841426215261894889754781370735552813938499349272801980762)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 122,
    recurrence4A4Square.coeff x * exceptional4.coeff (121 - x)) = _
  rw [show 122 = 108 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_121_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_122_prefix_zero :
    (∑ x ∈ Finset.range 109,
      recurrence4A4Square.coeff x * exceptional4.coeff (122 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (122 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_122 :
    recurrence4ExceptionalProduct.coeff 122 =
      (
        -(((803148655061417786676425862918269953289458 * 10 ^ 70 +
          2377976430686129868322914050422812612702004472289910178228528665654335) * 10 ^ 70 +
          6789781374845212296834289360427345754166669212253800710295217223969290)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 123,
    recurrence4A4Square.coeff x * exceptional4.coeff (122 - x)) = _
  rw [show 123 = 109 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_122_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_123_prefix_zero :
    (∑ x ∈ Finset.range 110,
      recurrence4A4Square.coeff x * exceptional4.coeff (123 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (123 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_123 :
    recurrence4ExceptionalProduct.coeff 123 =
      (
        (((3133476827711809408663101841102741754497573 * 10 ^ 70 +
          0122941685783721263230736438230854842781431968329719563372528720583045) * 10 ^ 70 +
          3813563854576037473097253938522763371370637625393343448697259641958522)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 124,
    recurrence4A4Square.coeff x * exceptional4.coeff (123 - x)) = _
  rw [show 124 = 110 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_123_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_124_prefix_zero :
    (∑ x ∈ Finset.range 111,
      recurrence4A4Square.coeff x * exceptional4.coeff (124 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (124 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_124 :
    recurrence4ExceptionalProduct.coeff 124 =
      (
        -(((11885887665701617148968094456232335269036671 * 10 ^ 70 +
          7441260720408429910701666712197151378826291213582283993648503225437035) * 10 ^ 70 +
          9047383202128845787025344000995167613953467273446070538351050042821435)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 125,
    recurrence4A4Square.coeff x * exceptional4.coeff (124 - x)) = _
  rw [show 125 = 111 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_124_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_125_prefix_zero :
    (∑ x ∈ Finset.range 112,
      recurrence4A4Square.coeff x * exceptional4.coeff (125 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (125 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_125 :
    recurrence4ExceptionalProduct.coeff 125 =
      (
        (((43877272933873765956658397016409340343015765 * 10 ^ 70 +
          4017618817163862076975255120398280468037582939430634740653756020143156) * 10 ^ 70 +
          5994391365110281633288541763651248488281785614198417898899679432491485)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 126,
    recurrence4A4Square.coeff x * exceptional4.coeff (125 - x)) = _
  rw [show 126 = 112 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_125_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_126_prefix_zero :
    (∑ x ∈ Finset.range 113,
      recurrence4A4Square.coeff x * exceptional4.coeff (126 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (126 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_126 :
    recurrence4ExceptionalProduct.coeff 126 =
      (
        -(((12135918741247051246098535970581031882381985 * 10 ^ 70 +
          7493932699433835069534932809344466876366111293792318558004916754791844) * 10 ^ 70 +
          0098049523384053768964362615487770024531185381782573226427596124169384)) /
        (1785787687194522429613 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 127,
    recurrence4A4Square.coeff x * exceptional4.coeff (126 - x)) = _
  rw [show 127 = 113 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_126_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_127_prefix_zero :
    (∑ x ∈ Finset.range 114,
      recurrence4A4Square.coeff x * exceptional4.coeff (127 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (127 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_127 :
    recurrence4ExceptionalProduct.coeff 127 =
      (
        (((552938408173771275028919947096519333004025949 * 10 ^ 70 +
          6626075415125401164400262326804744030093458057113850205219979508682316) * 10 ^ 70 +
          0970945196270791704042233531909822127353708907288872013065130020632898)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 128,
    recurrence4A4Square.coeff x * exceptional4.coeff (127 - x)) = _
  rw [show 128 = 114 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_127_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_128_prefix_zero :
    (∑ x ∈ Finset.range 115,
      recurrence4A4Square.coeff x * exceptional4.coeff (128 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (128 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_128 :
    recurrence4ExceptionalProduct.coeff 128 =
      (
        -(((1890158042256199260020197737010037193611451678 * 10 ^ 70 +
          6382541129325040764614599271587277741654672859015071252544117990386981) * 10 ^ 70 +
          9570024713942700429516035544035980833120080366504195035684627653957125)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 129,
    recurrence4A4Square.coeff x * exceptional4.coeff (128 - x)) = _
  rw [show 129 = 115 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_128_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_129_prefix_zero :
    (∑ x ∈ Finset.range 116,
      recurrence4A4Square.coeff x * exceptional4.coeff (129 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (129 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_129 :
    recurrence4ExceptionalProduct.coeff 129 =
      (
        (((6305564895814994287390763135764351235438803720 * 10 ^ 70 +
          6598480119074266614213803535038538267934987289309475329328714415801134) * 10 ^ 70 +
          8769562643403557974849643888373900001121562292647959365850546387736373)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 130,
    recurrence4A4Square.coeff x * exceptional4.coeff (129 - x)) = _
  rw [show 130 = 116 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_129_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_130_prefix_zero :
    (∑ x ∈ Finset.range 117,
      recurrence4A4Square.coeff x * exceptional4.coeff (130 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (130 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_130 :
    recurrence4ExceptionalProduct.coeff 130 =
      (
        -(((20538636893352231569024606573179191491049398187 * 10 ^ 70 +
          0298546446999412220839670691778459916725549375730398063423640276345311) * 10 ^ 70 +
          1148577589436735721025412190141436039906752767356170177813668183900878)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 131,
    recurrence4A4Square.coeff x * exceptional4.coeff (130 - x)) = _
  rw [show 131 = 117 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_130_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_131_prefix_zero :
    (∑ x ∈ Finset.range 118,
      recurrence4A4Square.coeff x * exceptional4.coeff (131 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (131 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_131 :
    recurrence4ExceptionalProduct.coeff 131 =
      (
        (((65348541370084990298361571997187722540788269250 * 10 ^ 70 +
          3586875876940638904102130801070290638050039266049284209570830795951540) * 10 ^ 70 +
          0442434453313999504983151324327522671389841621151552238773418779919984)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 132,
    recurrence4A4Square.coeff x * exceptional4.coeff (131 - x)) = _
  rw [show 132 = 118 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_131_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_132_prefix_zero :
    (∑ x ∈ Finset.range 119,
      recurrence4A4Square.coeff x * exceptional4.coeff (132 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (132 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_132 :
    recurrence4ExceptionalProduct.coeff 132 =
      (
        -(((203185615636598901317848062000688295472427324290 * 10 ^ 70 +
          0682658771501141900316627954571451050608212061484111581497238324447280) * 10 ^ 70 +
          2111500719129226161228146974662690074822769466096866665771797200193677)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 133,
    recurrence4A4Square.coeff x * exceptional4.coeff (132 - x)) = _
  rw [show 133 = 119 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_132_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_133_prefix_zero :
    (∑ x ∈ Finset.range 120,
      recurrence4A4Square.coeff x * exceptional4.coeff (133 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (133 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_133 :
    recurrence4ExceptionalProduct.coeff 133 =
      (
        (((617593732224549312826321456992163018996686134366 * 10 ^ 70 +
          9300923805088454984219769086891008612995590321969913579130955985411885) * 10 ^ 70 +
          8192541740802991847322391655548013491630408847073846350221004164679137)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 134,
    recurrence4A4Square.coeff x * exceptional4.coeff (133 - x)) = _
  rw [show 134 = 120 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_133_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_134_prefix_zero :
    (∑ x ∈ Finset.range 121,
      recurrence4A4Square.coeff x * exceptional4.coeff (134 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (134 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_134 :
    recurrence4ExceptionalProduct.coeff 134 =
      (
        -(((1835743284840214588715923871866139196437731505529 * 10 ^ 70 +
          8190228942710345812412522673732194878262671889022456176873855862329863) * 10 ^ 70 +
          1129344720138529707066312405779189269727632575006074452964801065407030)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 135,
    recurrence4A4Square.coeff x * exceptional4.coeff (134 - x)) = _
  rw [show 135 = 121 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_134_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_135_prefix_zero :
    (∑ x ∈ Finset.range 122,
      recurrence4A4Square.coeff x * exceptional4.coeff (135 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (135 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_135 :
    recurrence4ExceptionalProduct.coeff 135 =
      (
        (((5337704069114452465399800441873826131187585406083 * 10 ^ 70 +
          9976610706255136481885902720157022777315536094535982275832628647453039) * 10 ^ 70 +
          3490276912953275525710187477143435676036116726528891095294798983606936)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 136,
    recurrence4A4Square.coeff x * exceptional4.coeff (135 - x)) = _
  rw [show 136 = 122 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_135_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_136_prefix_zero :
    (∑ x ∈ Finset.range 123,
      recurrence4A4Square.coeff x * exceptional4.coeff (136 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (136 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_136 :
    recurrence4ExceptionalProduct.coeff 136 =
      (
        -(((15186384395503247704840354601647007733230860268924 * 10 ^ 70 +
          4884525658074841376465579035962980481304746660092018783336065125652887) * 10 ^ 70 +
          1443888652676563021179767583144787816230076376139132428543910207024997)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 137,
    recurrence4A4Square.coeff x * exceptional4.coeff (136 - x)) = _
  rw [show 137 = 123 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_136_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_137_prefix_zero :
    (∑ x ∈ Finset.range 124,
      recurrence4A4Square.coeff x * exceptional4.coeff (137 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (137 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_137 :
    recurrence4ExceptionalProduct.coeff 137 =
      (
        (((42288893129811509222656374590137702939436215950054 * 10 ^ 70 +
          4789604044188706639179139172648796907789161837902233516601732879043567) * 10 ^ 70 +
          9279565978855371266179356715486871801626889537397127619588063072126649)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 138,
    recurrence4A4Square.coeff x * exceptional4.coeff (137 - x)) = _
  rw [show 138 = 124 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_137_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_138_prefix_zero :
    (∑ x ∈ Finset.range 125,
      recurrence4A4Square.coeff x * exceptional4.coeff (138 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (138 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_138 :
    recurrence4ExceptionalProduct.coeff 138 =
      (
        -(((115286065224232905719794482490308346672947411946054 * 10 ^ 70 +
          3563562560411794425313059285511899867642537554597723074055831107177325) * 10 ^ 70 +
          6928298476342489699380050131277382663293323250044204439889994101089733)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 139,
    recurrence4A4Square.coeff x * exceptional4.coeff (138 - x)) = _
  rw [show 139 = 125 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_138_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_139_prefix_zero :
    (∑ x ∈ Finset.range 126,
      recurrence4A4Square.coeff x * exceptional4.coeff (139 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (139 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_139 :
    recurrence4ExceptionalProduct.coeff 139 =
      (
        (((23673463990450303192684759655657470333980633980704 * 10 ^ 70 +
          2452632762916973375286562293887560057508868143416364747427771948039745) * 10 ^ 70 +
          9790133101934774370775711491342005933742648296659705846811901943580007)) /
        (1785787687194522429613 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 140,
    recurrence4A4Square.coeff x * exceptional4.coeff (139 - x)) = _
  rw [show 140 = 126 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_139_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_140_prefix_zero :
    (∑ x ∈ Finset.range 127,
      recurrence4A4Square.coeff x * exceptional4.coeff (140 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (140 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_140 :
    recurrence4ExceptionalProduct.coeff 140 =
      (
        -(((804644652389313005061616838599159106295475397723936 * 10 ^ 70 +
          7156114577927653504475835531640701478853217502387507053078101613432439) * 10 ^ 70 +
          9605253055046237976242213940005309926309548933793807890426962066515550)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 141,
    recurrence4A4Square.coeff x * exceptional4.coeff (140 - x)) = _
  rw [show 141 = 127 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_140_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_141_prefix_zero :
    (∑ x ∈ Finset.range 128,
      recurrence4A4Square.coeff x * exceptional4.coeff (141 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (141 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_141 :
    recurrence4ExceptionalProduct.coeff 141 =
      (
        (((2060917617756859383278469788735820883175624825488234 * 10 ^ 70 +
          1412741167798887119257369934662932974427217423401864787009410727505225) * 10 ^ 70 +
          6094574064253784936086017842662398197440857757233805769322556933126394)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 142,
    recurrence4A4Square.coeff x * exceptional4.coeff (141 - x)) = _
  rw [show 142 = 128 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_141_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_142_prefix_zero :
    (∑ x ∈ Finset.range 129,
      recurrence4A4Square.coeff x * exceptional4.coeff (142 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (142 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_142 :
    recurrence4ExceptionalProduct.coeff 142 =
      (
        -(((5171973362459938911971442132887513769784567622078977 * 10 ^ 70 +
          0384786740656687391952860165138997839309805075973527399500897907946716) * 10 ^ 70 +
          7419353082917613409800238512593864872090031944693003117504482454569909)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 143,
    recurrence4A4Square.coeff x * exceptional4.coeff (142 - x)) = _
  rw [show 143 = 129 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_142_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_143_prefix_zero :
    (∑ x ∈ Finset.range 130,
      recurrence4A4Square.coeff x * exceptional4.coeff (143 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (143 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_143 :
    recurrence4ExceptionalProduct.coeff 143 =
      (
        (((12719436048961707281691931871889699180107304783533107 * 10 ^ 70 +
          7860850400391450747398020775157302358062112055932997139179909387349723) * 10 ^ 70 +
          6251473650995172226422287715816388644505551611182029745925202357992421)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 144,
    recurrence4A4Square.coeff x * exceptional4.coeff (143 - x)) = _
  rw [show 144 = 130 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_143_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_144_prefix_zero :
    (∑ x ∈ Finset.range 131,
      recurrence4A4Square.coeff x * exceptional4.coeff (144 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (144 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_144 :
    recurrence4ExceptionalProduct.coeff 144 =
      (
        -(((30659688415766812222230483191694871858260659425780396 * 10 ^ 70 +
          7921630475420166903128868698237534380199710001035272438780457285386149) * 10 ^ 70 +
          9386130601601794512489183491770084675091787038708770734018510878812673)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 145,
    recurrence4A4Square.coeff x * exceptional4.coeff (144 - x)) = _
  rw [show 145 = 131 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_144_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_145_prefix_zero :
    (∑ x ∈ Finset.range 132,
      recurrence4A4Square.coeff x * exceptional4.coeff (145 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (145 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_145 :
    recurrence4ExceptionalProduct.coeff 145 =
      (
        (((72447641604235015342537515032192734196480544206891743 * 10 ^ 70 +
          4657305333133677635871869521490824331201529214861670887720899948829029) * 10 ^ 70 +
          9552652240157912981826125488149017655897788534236992159739773690303449)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 146,
    recurrence4A4Square.coeff x * exceptional4.coeff (145 - x)) = _
  rw [show 146 = 132 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_145_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_146_prefix_zero :
    (∑ x ∈ Finset.range 133,
      recurrence4A4Square.coeff x * exceptional4.coeff (146 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (146 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_146 :
    recurrence4ExceptionalProduct.coeff 146 =
      (
        -(((167842526259651364086267273276429663083462647499656671 * 10 ^ 70 +
          3744770241952580180571593168193643684134511710703991288099996402290364) * 10 ^ 70 +
          0674882530994283389779856484552314209254962533451164581354936302053350)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 147,
    recurrence4A4Square.coeff x * exceptional4.coeff (146 - x)) = _
  rw [show 147 = 133 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_146_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_147_prefix_zero :
    (∑ x ∈ Finset.range 134,
      recurrence4A4Square.coeff x * exceptional4.coeff (147 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (147 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_147 :
    recurrence4ExceptionalProduct.coeff 147 =
      (
        (((381295925104852866542100259881017856261837682207233973 * 10 ^ 70 +
          9615935472316172291951766533485367678200123031818212991322907977953450) * 10 ^ 70 +
          2819775031106893103110860424693395726159657339098736968714488644842350)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 148,
    recurrence4A4Square.coeff x * exceptional4.coeff (147 - x)) = _
  rw [show 148 = 134 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_147_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_148_prefix_zero :
    (∑ x ∈ Finset.range 135,
      recurrence4A4Square.coeff x * exceptional4.coeff (148 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (148 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_148 :
    recurrence4ExceptionalProduct.coeff 148 =
      (
        -(((849498640584712471108233294421932357484044731910900307 * 10 ^ 70 +
          6991643830625957599546357315888928719603372492397741280824999958111810) * 10 ^ 70 +
          6568342832241067249351468352320152626816096334647598418471336631420066)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 149,
    recurrence4A4Square.coeff x * exceptional4.coeff (148 - x)) = _
  rw [show 149 = 135 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_148_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_149_prefix_zero :
    (∑ x ∈ Finset.range 136,
      recurrence4A4Square.coeff x * exceptional4.coeff (149 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (149 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_149 :
    recurrence4ExceptionalProduct.coeff 149 =
      (
        (((1856344490291760898066083094021628581956490515258902437 * 10 ^ 70 +
          7166120850696695373312996189880892709771974278614536943152495054067965) * 10 ^ 70 +
          2975465905680842674038049962022812499519302329520048932406222726714078)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 150,
    recurrence4A4Square.coeff x * exceptional4.coeff (149 - x)) = _
  rw [show 150 = 136 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_149_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_150_prefix_zero :
    (∑ x ∈ Finset.range 137,
      recurrence4A4Square.coeff x * exceptional4.coeff (150 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (150 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_150 :
    recurrence4ExceptionalProduct.coeff 150 =
      (
        -(((3979257431969905475284849594522398409886437705883248897 * 10 ^ 70 +
          0759398457724073681823004062059563000774048671226262918116820251858829) * 10 ^ 70 +
          3341099424251577272835793138124831802919962856768080943397507397278574)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 151,
    recurrence4A4Square.coeff x * exceptional4.coeff (150 - x)) = _
  rw [show 151 = 137 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_150_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_151_prefix_zero :
    (∑ x ∈ Finset.range 138,
      recurrence4A4Square.coeff x * exceptional4.coeff (151 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (151 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_151 :
    recurrence4ExceptionalProduct.coeff 151 =
      (
        (((8368405048101099219462928339995753513120432053551758339 * 10 ^ 70 +
          8589117564015968573050056759506107576182637675493119240642351508602606) * 10 ^ 70 +
          3157291677260596526918472862143507953802333417287742999079855253225818)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 152,
    recurrence4A4Square.coeff x * exceptional4.coeff (151 - x)) = _
  rw [show 152 = 138 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_151_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_152_prefix_zero :
    (∑ x ∈ Finset.range 139,
      recurrence4A4Square.coeff x * exceptional4.coeff (152 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (152 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_152 :
    recurrence4ExceptionalProduct.coeff 152 =
      (
        -(((17267430546362707397654058142981878329169225580622741464 * 10 ^ 70 +
          1835761865135437558855371087095705281030779778289400910076217305178394) * 10 ^ 70 +
          2213934102955374396924426220925248869744541962766805824465292808551987)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 153,
    recurrence4A4Square.coeff x * exceptional4.coeff (152 - x)) = _
  rw [show 153 = 139 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_152_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_153_prefix_zero :
    (∑ x ∈ Finset.range 140,
      recurrence4A4Square.coeff x * exceptional4.coeff (153 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (153 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_153 :
    recurrence4ExceptionalProduct.coeff 153 =
      (
        (((2689420020422876378639838036204386126503266246525376418 * 10 ^ 70 +
          9678494286982605548334664596932491621560380466912729299097274484821328) * 10 ^ 70 +
          2254914518435959372390672949023829852663545562822000891867874636996853)) /
        (1785787687194522429613 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 154,
    recurrence4A4Square.coeff x * exceptional4.coeff (153 - x)) = _
  rw [show 154 = 140 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_153_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_154_prefix_zero :
    (∑ x ∈ Finset.range 141,
      recurrence4A4Square.coeff x * exceptional4.coeff (154 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (154 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_154 :
    recurrence4ExceptionalProduct.coeff 154 =
      (
        -(((69471743735676332453534473895291997512831549303860994690 * 10 ^ 70 +
          5526911548944146015858954916864178395481861723508939740165418022603133) * 10 ^ 70 +
          6861333440761217627081179035988295636275053910571994779366451836091727)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 155,
    recurrence4A4Square.coeff x * exceptional4.coeff (154 - x)) = _
  rw [show 155 = 141 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_154_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_155_prefix_zero :
    (∑ x ∈ Finset.range 142,
      recurrence4A4Square.coeff x * exceptional4.coeff (155 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (155 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_155 :
    recurrence4ExceptionalProduct.coeff 155 =
      (
        (((135483687221863303738605725004962065943394581298734511047 * 10 ^ 70 +
          2426548505447982609210254200661211445789714336269789801081980825098640) * 10 ^ 70 +
          3404420298514376034217596753037132266625851266666254076198692129276669)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 156,
    recurrence4A4Square.coeff x * exceptional4.coeff (155 - x)) = _
  rw [show 156 = 142 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_155_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_156_prefix_zero :
    (∑ x ∈ Finset.range 143,
      recurrence4A4Square.coeff x * exceptional4.coeff (156 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (156 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_156 :
    recurrence4ExceptionalProduct.coeff 156 =
      (
        -(((259344538753474119296595834723023446976432704235206066742 * 10 ^ 70 +
          9570873609443478544076806960220799255272466767196263204237189529553145) * 10 ^ 70 +
          1026779624829567447556879291089761644224412634113292224870163259600617)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 157,
    recurrence4A4Square.coeff x * exceptional4.coeff (156 - x)) = _
  rw [show 157 = 143 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_156_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_157_prefix_zero :
    (∑ x ∈ Finset.range 144,
      recurrence4A4Square.coeff x * exceptional4.coeff (157 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (157 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_157 :
    recurrence4ExceptionalProduct.coeff 157 =
      (
        (((37486249367484765778293095062069653023210811399826210565 * 10 ^ 70 +
          9533978840576104141767823275495541723218799375893000057364426942781251) * 10 ^ 70 +
          5949345973493731543200253021191478606314094915125252416146243414564091)) /
        (1785787687194522429613 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 158,
    recurrence4A4Square.coeff x * exceptional4.coeff (157 - x)) = _
  rw [show 158 = 144 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_157_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_158_prefix_zero :
    (∑ x ∈ Finset.range 145,
      recurrence4A4Square.coeff x * exceptional4.coeff (158 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (158 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_158 :
    recurrence4ExceptionalProduct.coeff 158 =
      (
        -(((898952593793575041217358242829545049322844543736443511520 * 10 ^ 70 +
          1680452676357636629781557951079943571039747747063133607903456622527398) * 10 ^ 70 +
          6425512172146216164930212337659877411234701466831438662947664407912823)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 159,
    recurrence4A4Square.coeff x * exceptional4.coeff (158 - x)) = _
  rw [show 159 = 145 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_158_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_159_prefix_zero :
    (∑ x ∈ Finset.range 146,
      recurrence4A4Square.coeff x * exceptional4.coeff (159 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (159 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_159 :
    recurrence4ExceptionalProduct.coeff 159 =
      (
        (((1628076621334449617284541260621839311428332712768141569733 * 10 ^ 70 +
          6065644713273183283618108884758602293782763250424764487966168052380376) * 10 ^ 70 +
          7532131069179667563072276120936537695236442465145458056566238579037647)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 160,
    recurrence4A4Square.coeff x * exceptional4.coeff (159 - x)) = _
  rw [show 160 = 146 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_159_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_160_prefix_zero :
    (∑ x ∈ Finset.range 147,
      recurrence4A4Square.coeff x * exceptional4.coeff (160 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (160 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_160 :
    recurrence4ExceptionalProduct.coeff 160 =
      (
        -(((2895084662670980530087875797870500832046053460096630877036 * 10 ^ 70 +
          6650445762825630638838985750863183741542475476787596004712516846609374) * 10 ^ 70 +
          3868226938169530365283099998357090615778973907315944972459684166465200)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 161,
    recurrence4A4Square.coeff x * exceptional4.coeff (160 - x)) = _
  rw [show 161 = 147 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_160_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_161_prefix_zero :
    (∑ x ∈ Finset.range 148,
      recurrence4A4Square.coeff x * exceptional4.coeff (161 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (161 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_161 :
    recurrence4ExceptionalProduct.coeff 161 =
      (
        (((5055059878372428703762730916952664716635305160779824339079 * 10 ^ 70 +
          2565838513311365599034944801512226993074662163959768612682070328085153) * 10 ^ 70 +
          3268811691532943222633964452185134905138838671303716378897251084938992)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 162,
    recurrence4A4Square.coeff x * exceptional4.coeff (161 - x)) = _
  rw [show 162 = 148 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_161_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_162_prefix_zero :
    (∑ x ∈ Finset.range 149,
      recurrence4A4Square.coeff x * exceptional4.coeff (162 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (162 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_162 :
    recurrence4ExceptionalProduct.coeff 162 =
      (
        -(((8667596592187672278595884729390713966506828173556704859587 * 10 ^ 70 +
          5208441345941246971810644115350982431949896822011804694751076020767704) * 10 ^ 70 +
          6596150370387253451516615478273889307185105589413068274279772340140698)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 163,
    recurrence4A4Square.coeff x * exceptional4.coeff (162 - x)) = _
  rw [show 163 = 149 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_162_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_163_prefix_zero :
    (∑ x ∈ Finset.range 150,
      recurrence4A4Square.coeff x * exceptional4.coeff (163 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (163 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_163 :
    recurrence4ExceptionalProduct.coeff 163 =
      (
        (((14595055142105497160671761922851325779696033685361218259348 * 10 ^ 70 +
          8324099156550926696268911948848526189878639549303385381820731423089318) * 10 ^ 70 +
          8309791292408936275420962706389424967343183806513185264695089156650758)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 164,
    recurrence4A4Square.coeff x * exceptional4.coeff (163 - x)) = _
  rw [show 164 = 150 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_163_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_164_prefix_zero :
    (∑ x ∈ Finset.range 151,
      recurrence4A4Square.coeff x * exceptional4.coeff (164 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (164 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_164 :
    recurrence4ExceptionalProduct.coeff 164 =
      (
        -(((24136449831653435755406684971421433627363772304290714789256 * 10 ^ 70 +
          6741392976125555304634146923667825075912860892013697415822583910678805) * 10 ^ 70 +
          4518688453656377000235665472782179608502664592187911997112032804396209)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 165,
    recurrence4A4Square.coeff x * exceptional4.coeff (164 - x)) = _
  rw [show 165 = 151 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_164_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_165_prefix_zero :
    (∑ x ∈ Finset.range 152,
      recurrence4A4Square.coeff x * exceptional4.coeff (165 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (165 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_165 :
    recurrence4ExceptionalProduct.coeff 165 =
      (
        (((39203627261406329125850456135165562758437520906265937797355 * 10 ^ 70 +
          5384674624649519550727880494959803992330685314017580153702064178450477) * 10 ^ 70 +
          2034872696878860725521109651194153082772139574992804441545109546770527)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 166,
    recurrence4A4Square.coeff x * exceptional4.coeff (165 - x)) = _
  rw [show 166 = 152 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_165_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_166_prefix_zero :
    (∑ x ∈ Finset.range 153,
      recurrence4A4Square.coeff x * exceptional4.coeff (166 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (166 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_166 :
    recurrence4ExceptionalProduct.coeff 166 =
      (
        -(((62544286767753303915983523758616316301223191004982989235324 * 10 ^ 70 +
          4595758290221325134188791471974571665732295547549254947453819922974832) * 10 ^ 70 +
          9467737251842178514064929319263264738989767678773149800297037174527203)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 167,
    recurrence4A4Square.coeff x * exceptional4.coeff (166 - x)) = _
  rw [show 167 = 153 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_166_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_167_prefix_zero :
    (∑ x ∈ Finset.range 154,
      recurrence4A4Square.coeff x * exceptional4.coeff (167 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (167 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_167 :
    recurrence4ExceptionalProduct.coeff 167 =
      (
        (((98012090089810932779988209149674376832058555696637457960753 * 10 ^ 70 +
          5795694398974822726355978250091224191210381314103396868498467607483876) * 10 ^ 70 +
          3995975236297705325787811092001162230897378333518567754459328798966307)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 168,
    recurrence4A4Square.coeff x * exceptional4.coeff (167 - x)) = _
  rw [show 168 = 154 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_167_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_168_prefix_zero :
    (∑ x ∈ Finset.range 155,
      recurrence4A4Square.coeff x * exceptional4.coeff (168 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (168 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_168 :
    recurrence4ExceptionalProduct.coeff 168 =
      (
        -(((150877036548865435326303135098832328827335105200985059046787 * 10 ^ 70 +
          3133279915365646427762170235112076183145609657509584310947290806927489) * 10 ^ 70 +
          5543183848075351536043902371006107322019962577397946013539607486972079)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 169,
    recurrence4A4Square.coeff x * exceptional4.coeff (168 - x)) = _
  rw [show 169 = 155 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_168_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_169_prefix_zero :
    (∑ x ∈ Finset.range 156,
      recurrence4A4Square.coeff x * exceptional4.coeff (169 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (169 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_169 :
    recurrence4ExceptionalProduct.coeff 169 =
      (
        (((228159120541226905066361685558954749495553285604582960188838 * 10 ^ 70 +
          0976064585833328928419469418286042961084455656818321393616655658904327) * 10 ^ 70 +
          9838754888926648759191345390526856449897729971542806760931605737387829)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 170,
    recurrence4A4Square.coeff x * exceptional4.coeff (169 - x)) = _
  rw [show 170 = 156 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_169_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_170_prefix_zero :
    (∑ x ∈ Finset.range 157,
      recurrence4A4Square.coeff x * exceptional4.coeff (170 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (170 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_170 :
    recurrence4ExceptionalProduct.coeff 170 =
      (
        -(((338955188232015597718714426713989544195566213276410110671260 * 10 ^ 70 +
          5233147695327555303936842598264371703197440851077134229299823419373113) * 10 ^ 70 +
          2891057293150522214175221086917408898678316835489471217533269651070862)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 171,
    recurrence4A4Square.coeff x * exceptional4.coeff (170 - x)) = _
  rw [show 171 = 157 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_170_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_171_prefix_zero :
    (∑ x ∈ Finset.range 158,
      recurrence4A4Square.coeff x * exceptional4.coeff (171 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (171 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_171 :
    recurrence4ExceptionalProduct.coeff 171 =
      (
        (((494713728866315368594427408768424536195867449850793514904803 * 10 ^ 70 +
          3444719127952557723067703786469011319582320754358829895491671048813618) * 10 ^ 70 +
          6452355191750278384143042616177024640823974259808786594751475074663832)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 172,
    recurrence4A4Square.coeff x * exceptional4.coeff (171 - x)) = _
  rw [show 172 = 158 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_171_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_172_prefix_zero :
    (∑ x ∈ Finset.range 159,
      recurrence4A4Square.coeff x * exceptional4.coeff (172 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (172 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_172 :
    recurrence4ExceptionalProduct.coeff 172 =
      (
        -(((709396839155693475154004169872590788385934176796779837595675 * 10 ^ 70 +
          0451878558489735277796904835971842546331970680569730918880391522674817) * 10 ^ 70 +
          0501169685554742214951309541925353405921999651948347981056293022679440)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 173,
    recurrence4A4Square.coeff x * exceptional4.coeff (172 - x)) = _
  rw [show 173 = 159 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_172_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_173_prefix_zero :
    (∑ x ∈ Finset.range 160,
      recurrence4A4Square.coeff x * exceptional4.coeff (173 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (173 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_173 :
    recurrence4ExceptionalProduct.coeff 173 =
      (
        (((999455535681495762843337603747627315729905283790483789476514 * 10 ^ 70 +
          8103219553935885013349568945612910918427744700211176455089762893484512) * 10 ^ 70 +
          2554802312907764334254038132347181067180066370585128743191920708765124)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 174,
    recurrence4A4Square.coeff x * exceptional4.coeff (173 - x)) = _
  rw [show 174 = 160 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_173_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_174_prefix_zero :
    (∑ x ∈ Finset.range 161,
      recurrence4A4Square.coeff x * exceptional4.coeff (174 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (174 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_174 :
    recurrence4ExceptionalProduct.coeff 174 =
      (
        -(((1383537562745497566745698600981654533236029332345235279568893 * 10 ^ 70 +
          3412806279419422882102819779940809133805963193985862051980915528325407) * 10 ^ 70 +
          4279624177292675571013368567212954845854735676844822519572725278514657)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 175,
    recurrence4A4Square.coeff x * exceptional4.coeff (174 - x)) = _
  rw [show 175 = 161 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_174_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_175_prefix_zero :
    (∑ x ∈ Finset.range 162,
      recurrence4A4Square.coeff x * exceptional4.coeff (175 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (175 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_175 :
    recurrence4ExceptionalProduct.coeff 175 =
      (
        (((1881849905467114275703931569849533507933758865365591938811489 * 10 ^ 70 +
          2205728026224073410339425691131869422912034419915983288076703575116498) * 10 ^ 70 +
          7729457747646935736109018550107680118396138584630177405437884522308803)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 176,
    recurrence4A4Square.coeff x * exceptional4.coeff (175 - x)) = _
  rw [show 176 = 162 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_175_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_176_prefix_zero :
    (∑ x ∈ Finset.range 163,
      recurrence4A4Square.coeff x * exceptional4.coeff (176 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (176 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_176 :
    recurrence4ExceptionalProduct.coeff 176 =
      (
        -(((2515115176133095642024918892332122494116946609561940487982783 * 10 ^ 70 +
          0759867352963277192449593650469997459348987780168841610334753705355201) * 10 ^ 70 +
          6320881257981317243570377487473439745800091376249980492323423228986686)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 177,
    recurrence4A4Square.coeff x * exceptional4.coeff (176 - x)) = _
  rw [show 177 = 163 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_176_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_177_prefix_zero :
    (∑ x ∈ Finset.range 164,
      recurrence4A4Square.coeff x * exceptional4.coeff (177 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (177 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_177 :
    recurrence4ExceptionalProduct.coeff 177 =
      (
        (((3303094506555780649906524184461499902402332827278699964637071 * 10 ^ 70 +
          4554682690890927069950481012573568217948080374125372668315104804283833) * 10 ^ 70 +
          3938322874269519656624763355804402420341408736893156937769885694924218)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 178,
    recurrence4A4Square.coeff x * exceptional4.coeff (177 - x)) = _
  rw [show 178 = 164 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_177_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_178_prefix_zero :
    (∑ x ∈ Finset.range 165,
      recurrence4A4Square.coeff x * exceptional4.coeff (178 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (178 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_178 :
    recurrence4ExceptionalProduct.coeff 178 =
      (
        -(((4262699909801587073654741647821833306931596221524337402600788 * 10 ^ 70 +
          3759527683280871291306218901515082717280970983278505800330608188236689) * 10 ^ 70 +
          6131242985194828400709869588526746948263643667126242342988516433566006)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 179,
    recurrence4A4Square.coeff x * exceptional4.coeff (178 - x)) = _
  rw [show 179 = 165 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_178_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_179_prefix_zero :
    (∑ x ∈ Finset.range 166,
      recurrence4A4Square.coeff x * exceptional4.coeff (179 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (179 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_179 :
    recurrence4ExceptionalProduct.coeff 179 =
      (
        (((5405783441059939657601901400591116512141744610362878483509202 * 10 ^ 70 +
          6296200710027568342838048095063053223177913644029029942023237842584426) * 10 ^ 70 +
          8346586279944822076194861318448771066495366774052514462002851165130106)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 180,
    recurrence4A4Square.coeff x * exceptional4.coeff (179 - x)) = _
  rw [show 180 = 166 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_179_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_180_prefix_zero :
    (∑ x ∈ Finset.range 167,
      recurrence4A4Square.coeff x * exceptional4.coeff (180 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (180 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_180 :
    recurrence4ExceptionalProduct.coeff 180 =
      (
        -(((6736762333560098468080324413304656976069562867826646113218390 * 10 ^ 70 +
          9593254971064954129490464815028053940477091197250445196915366605981762) * 10 ^ 70 +
          8869350720208384162526450372277182764248791280622922511652586480986118)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 181,
    recurrence4A4Square.coeff x * exceptional4.coeff (180 - x)) = _
  rw [show 181 = 167 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_180_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_181_prefix_zero :
    (∑ x ∈ Finset.range 168,
      recurrence4A4Square.coeff x * exceptional4.coeff (181 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (181 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_181 :
    recurrence4ExceptionalProduct.coeff 181 =
      (
        (((8250308472080518620856777036905721782880489343085837563407219 * 10 ^ 70 +
          7907838895530706861463968843701856322932111265874712030501343006814645) * 10 ^ 70 +
          2782146515110476103553438569315879914989287049954297902125820574377002)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 182,
    recurrence4A4Square.coeff x * exceptional4.coeff (181 - x)) = _
  rw [show 182 = 168 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_181_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_182_prefix_zero :
    (∑ x ∈ Finset.range 169,
      recurrence4A4Square.coeff x * exceptional4.coeff (182 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (182 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_182 :
    recurrence4ExceptionalProduct.coeff 182 =
      (
        -(((9929384385136143259980023046883112470963917086982910517032423 * 10 ^ 70 +
          3859937391361118983287455012575738212827999046409196189592656362510016) * 10 ^ 70 +
          3340864866115925055554242560006108255859314076281309825285908508768227)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 183,
    recurrence4A4Square.coeff x * exceptional4.coeff (182 - x)) = _
  rw [show 183 = 169 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_182_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_183_prefix_zero :
    (∑ x ∈ Finset.range 170,
      recurrence4A4Square.coeff x * exceptional4.coeff (183 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (183 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_183 :
    recurrence4ExceptionalProduct.coeff 183 =
      (
        (((11743933015236872473581938904575194257883238139547481979262254 * 10 ^ 70 +
          6863596273328984779320428906432387516573618028627938497498448971911444) * 10 ^ 70 +
          2879197870216859920392886543882533502804461166901035077940086670436053)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 184,
    recurrence4A4Square.coeff x * exceptional4.coeff (183 - x)) = _
  rw [show 184 = 170 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_183_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_184_prefix_zero :
    (∑ x ∈ Finset.range 171,
      recurrence4A4Square.coeff x * exceptional4.coeff (184 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (184 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_184 :
    recurrence4ExceptionalProduct.coeff 184 =
      (
        -(((13650513418931765074953648813040208242485746039168385598942853 * 10 ^ 70 +
          7642972027091546687500497896080591188286057135786018977398191064888624) * 10 ^ 70 +
          4376890213994918751014443594760418709074015990614670944312615364088598)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 185,
    recurrence4A4Square.coeff x * exceptional4.coeff (184 - x)) = _
  rw [show 185 = 171 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_184_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_185_prefix_zero :
    (∑ x ∈ Finset.range 172,
      recurrence4A4Square.coeff x * exceptional4.coeff (185 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (185 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_185 :
    recurrence4ExceptionalProduct.coeff 185 =
      (
        (((15593112564514640511771658565600737560480351866794647528175841 * 10 ^ 70 +
          9610502599386399747468198481111274300423877955332821518872713058306541) * 10 ^ 70 +
          1111567721289523625792833587662043217785215157352545107769660632098074)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 186,
    recurrence4A4Square.coeff x * exceptional4.coeff (185 - x)) = _
  rw [show 186 = 172 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_185_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_186_prefix_zero :
    (∑ x ∈ Finset.range 173,
      recurrence4A4Square.coeff x * exceptional4.coeff (186 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (186 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_186 :
    recurrence4ExceptionalProduct.coeff 186 =
      (
        -(((17505255047700955109258341251939529440845187503459829417220055 * 10 ^ 70 +
          2597175866480827387687190913381579876834986183034391513868021400648018) * 10 ^ 70 +
          0264296785405130514725274579191204826561430811581414713647414018906439)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 187,
    recurrence4A4Square.coeff x * exceptional4.coeff (186 - x)) = _
  rw [show 187 = 173 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_186_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_187_prefix_zero :
    (∑ x ∈ Finset.range 174,
      recurrence4A4Square.coeff x * exceptional4.coeff (187 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (187 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_187 :
    recurrence4ExceptionalProduct.coeff 187 =
      (
        (((19313386943733274981301563117912298102822697231148970045113787 * 10 ^ 70 +
          1846558451766936344774937963425879798343607870915375924854047612705099) * 10 ^ 70 +
          0952405406847366953270116808374889713165275640955078188420920294707155)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 188,
    recurrence4A4Square.coeff x * exceptional4.coeff (187 - x)) = _
  rw [show 188 = 174 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_187_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_188_prefix_zero :
    (∑ x ∈ Finset.range 175,
      recurrence4A4Square.coeff x * exceptional4.coeff (188 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (188 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_188 :
    recurrence4ExceptionalProduct.coeff 188 =
      (
        -(((20941344658948906792539543832469181294933027658075373935175767 * 10 ^ 70 +
          0646227900881983358468147174552486898490490901611132697291450380447453) * 10 ^ 70 +
          0978914444939887475896653559266388167433424240838753136107068433031680)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 189,
    recurrence4A4Square.coeff x * exceptional4.coeff (188 - x)) = _
  rw [show 189 = 175 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_188_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_189_prefix_zero :
    (∑ x ∈ Finset.range 176,
      recurrence4A4Square.coeff x * exceptional4.coeff (189 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (189 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_189 :
    recurrence4ExceptionalProduct.coeff 189 =
      (
        (((22315558370938264906595061249080719333137079014560371828837419 * 10 ^ 70 +
          0515997445164332074841185395857904950590243500513157621257217753516514) * 10 ^ 70 +
          1304204038781862702834218741396336390889598008897002762125479549489524)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 190,
    recurrence4A4Square.coeff x * exceptional4.coeff (189 - x)) = _
  rw [show 190 = 176 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_189_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_190_prefix_zero :
    (∑ x ∈ Finset.range 177,
      recurrence4A4Square.coeff x * exceptional4.coeff (190 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (190 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_190 :
    recurrence4ExceptionalProduct.coeff 190 =
      (
        -(((23370508883422632144416942307650368327100400545554747679040940 * 10 ^ 70 +
          7146654454611670610000292441969839498597022721647388738251405653701791) * 10 ^ 70 +
          7242304225340294802541172832082520533820327353811271092452597471751074)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 191,
    recurrence4A4Square.coeff x * exceptional4.coeff (190 - x)) = _
  rw [show 191 = 177 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_190_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_191_prefix_zero :
    (∑ x ∈ Finset.range 178,
      recurrence4A4Square.coeff x * exceptional4.coeff (191 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (191 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_191 :
    recurrence4ExceptionalProduct.coeff 191 =
      (
        (((24053880682519150634443328970475066668702045355078518432712218 * 10 ^ 70 +
          0237548526090608397710243145110873113903725428273627205839525164673492) * 10 ^ 70 +
          0776623827984973650384788131229101593857916150556223061713117128024612)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 192,
    recurrence4A4Square.coeff x * exceptional4.coeff (191 - x)) = _
  rw [show 192 = 178 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_191_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_192_prefix_zero :
    (∑ x ∈ Finset.range 179,
      recurrence4A4Square.coeff x * exceptional4.coeff (192 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (192 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_192 :
    recurrence4ExceptionalProduct.coeff 192 =
      (
        -(((1871603826116538894042464967870657206593049722741573276108524 * 10 ^ 70 +
          3061685733611193136772987157527223337054744763335099176445956703796497) * 10 ^ 70 +
          9642476560329366711653444283748953780509416950893976355221334839099747)) /
        (1785787687194522429613 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 193,
    recurrence4A4Square.coeff x * exceptional4.coeff (192 - x)) = _
  rw [show 193 = 179 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_192_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_193_prefix_zero :
    (∑ x ∈ Finset.range 180,
      recurrence4A4Square.coeff x * exceptional4.coeff (193 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (193 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_193 :
    recurrence4ExceptionalProduct.coeff 193 =
      (
        (((24187018168254718007007104208205733581467745358261418833947253 * 10 ^ 70 +
          1358715639145424414980662660003530250259344059196474460460139636533465) * 10 ^ 70 +
          7914693617878868309651994256157902056578864137097885709523979329047515)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 194,
    recurrence4A4Square.coeff x * exceptional4.coeff (193 - x)) = _
  rw [show 194 = 180 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_193_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_194_prefix_zero :
    (∑ x ∈ Finset.range 181,
      recurrence4A4Square.coeff x * exceptional4.coeff (194 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (194 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_194 :
    recurrence4ExceptionalProduct.coeff 194 =
      (
        -(((23629652188217811877936114869192464038744899899377875185764892 * 10 ^ 70 +
          1586964860429951965636033019752390740686919169743372727169694562255627) * 10 ^ 70 +
          0588094896922896302185689939304629924588199131294956395545635890629741)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 195,
    recurrence4A4Square.coeff x * exceptional4.coeff (194 - x)) = _
  rw [show 195 = 181 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_194_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_195_prefix_zero :
    (∑ x ∈ Finset.range 182,
      recurrence4A4Square.coeff x * exceptional4.coeff (195 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (195 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_195 :
    recurrence4ExceptionalProduct.coeff 195 =
      (
        (((22687075497761924318407378824730248656046132003703606944212030 * 10 ^ 70 +
          8854015724410813552406445464209791802905928517422948183713956495110979) * 10 ^ 70 +
          9434182620266825398018727573636511705937476819726810074838977697310163)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 196,
    recurrence4A4Square.coeff x * exceptional4.coeff (195 - x)) = _
  rw [show 196 = 182 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_195_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_196_prefix_zero :
    (∑ x ∈ Finset.range 183,
      recurrence4A4Square.coeff x * exceptional4.coeff (196 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (196 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_196 :
    recurrence4ExceptionalProduct.coeff 196 =
      (
        -(((21406288361672123955254652539168464332204411418138657879802700 * 10 ^ 70 +
          6079644411710554333546250868232008560270314675251245316631760659354906) * 10 ^ 70 +
          0686730202038942142946707453286760595059212360223574297176511154684510)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 197,
    recurrence4A4Square.coeff x * exceptional4.coeff (196 - x)) = _
  rw [show 197 = 183 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_196_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_197_prefix_zero :
    (∑ x ∈ Finset.range 184,
      recurrence4A4Square.coeff x * exceptional4.coeff (197 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (197 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_197 :
    recurrence4ExceptionalProduct.coeff 197 =
      (
        (((19849090529382246236903885610985677571762966203084027481389114 * 10 ^ 70 +
          1371425859850663486485340282994360119422106692366546005663968526604934) * 10 ^ 70 +
          6931060091496431437712345129592921751458416167960696046819272185395284)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 198,
    recurrence4A4Square.coeff x * exceptional4.coeff (197 - x)) = _
  rw [show 198 = 184 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_197_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_198_prefix_zero :
    (∑ x ∈ Finset.range 185,
      recurrence4A4Square.coeff x * exceptional4.coeff (198 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (198 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_198 :
    recurrence4ExceptionalProduct.coeff 198 =
      (
        -(((18087152451311695365754099100554769983008476905504390349171788 * 10 ^ 70 +
          0054318407802217039530843306827060415210855842528422366993382734454966) * 10 ^ 70 +
          1167501940845643420688310102057166738449595908519395991713304797903429)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 199,
    recurrence4A4Square.coeff x * exceptional4.coeff (198 - x)) = _
  rw [show 199 = 185 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_198_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_199_prefix_zero :
    (∑ x ∈ Finset.range 186,
      recurrence4A4Square.coeff x * exceptional4.coeff (199 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (199 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_199 :
    recurrence4ExceptionalProduct.coeff 199 =
      (
        (((16196580576241955806364610615082430766768346817687469139943944 * 10 ^ 70 +
          6652451921763485899934753594853869993876961008281880943057982189710766) * 10 ^ 70 +
          4743124972605359080602155760995160810705887586156458663852950475847935)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 200,
    recurrence4A4Square.coeff x * exceptional4.coeff (199 - x)) = _
  rw [show 200 = 186 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_199_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_200_prefix_zero :
    (∑ x ∈ Finset.range 187,
      recurrence4A4Square.coeff x * exceptional4.coeff (200 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (200 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_200 :
    recurrence4ExceptionalProduct.coeff 200 =
      (
        -(((14252546765194635018816542053778009440474668254890276486138539 * 10 ^ 70 +
          5754010782747955758115813073154471604615058611384547347815538364089909) * 10 ^ 70 +
          2887553688510108691730478139190637839707293900041104372007729174467573)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 201,
    recurrence4A4Square.coeff x * exceptional4.coeff (200 - x)) = _
  rw [show 201 = 187 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_200_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_201_prefix_zero :
    (∑ x ∈ Finset.range 188,
      recurrence4A4Square.coeff x * exceptional4.coeff (201 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (201 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_201 :
    recurrence4ExceptionalProduct.coeff 201 =
      (
        (((12324500208808288867516640097921831856250767206125265786685273 * 10 ^ 70 +
          2992015974173405776187033522361141176821506671299792913273302276479872) * 10 ^ 70 +
          8602470775412444836506715825444004903295619425571450481456224669113973)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 202,
    recurrence4A4Square.coeff x * exceptional4.coeff (201 - x)) = _
  rw [show 202 = 188 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_201_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_202_prefix_zero :
    (∑ x ∈ Finset.range 189,
      recurrence4A4Square.coeff x * exceptional4.coeff (202 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (202 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_202 :
    recurrence4ExceptionalProduct.coeff 202 =
      (
        -(((805566617956983577613914371592370090327333417942852757417763 * 10 ^ 70 +
          9679505045328493732959329393213520223695917345329485802989254769501808) * 10 ^ 70 +
          7005900447488806686670912125151230378476849051039162555476185545334331)) /
        (1785787687194522429613 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 203,
    recurrence4A4Square.coeff x * exceptional4.coeff (202 - x)) = _
  rw [show 203 = 189 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_202_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_203_prefix_zero :
    (∑ x ∈ Finset.range 190,
      recurrence4A4Square.coeff x * exceptional4.coeff (203 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (203 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_203 :
    recurrence4ExceptionalProduct.coeff 203 =
      (
        (((8743980277591481416642878576519590473739842246652651363932904 * 10 ^ 70 +
          3539701629817449313158936734022195698056418940852517425342734911499893) * 10 ^ 70 +
          2582136443698617156434077368616918570766770166519659384093636966927077)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 204,
    recurrence4A4Square.coeff x * exceptional4.coeff (203 - x)) = _
  rw [show 204 = 190 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_203_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_204_prefix_zero :
    (∑ x ∈ Finset.range 191,
      recurrence4A4Square.coeff x * exceptional4.coeff (204 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (204 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_204 :
    recurrence4ExceptionalProduct.coeff 204 =
      (
        -(((7173842560417922685014384390343382735589190082971852176622745 * 10 ^ 70 +
          4488290613504427547690657839528992711892861191791280508995951985997019) * 10 ^ 70 +
          9055147329144761737315692771481141838101878112003365938508478324232737)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 205,
    recurrence4A4Square.coeff x * exceptional4.coeff (204 - x)) = _
  rw [show 205 = 191 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_204_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_205_prefix_zero :
    (∑ x ∈ Finset.range 192,
      recurrence4A4Square.coeff x * exceptional4.coeff (205 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (205 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_205 :
    recurrence4ExceptionalProduct.coeff 205 =
      (
        (((5783111147803223013010036708939323813187964250886895011901361 * 10 ^ 70 +
          6269211212100685620874419747340461076103970601613756191378179260955528) * 10 ^ 70 +
          1070094395960168076256744780704363212938874852660421680470017599612123)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 206,
    recurrence4A4Square.coeff x * exceptional4.coeff (205 - x)) = _
  rw [show 206 = 192 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_205_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_206_prefix_zero :
    (∑ x ∈ Finset.range 193,
      recurrence4A4Square.coeff x * exceptional4.coeff (206 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (206 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_206 :
    recurrence4ExceptionalProduct.coeff 206 =
      (
        -(((4580640693785434919865492189516302850781348548770632220602452 * 10 ^ 70 +
          8663747031627099167126917153168320180012444577051736876249134948042820) * 10 ^ 70 +
          1532360455073270025412951685765087829634940887881362620064103914711965)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 207,
    recurrence4A4Square.coeff x * exceptional4.coeff (206 - x)) = _
  rw [show 207 = 193 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_206_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_207_prefix_zero :
    (∑ x ∈ Finset.range 194,
      recurrence4A4Square.coeff x * exceptional4.coeff (207 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (207 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_207 :
    recurrence4ExceptionalProduct.coeff 207 =
      (
        (((3564783193382342475638510232658289884325276547943502863088373 * 10 ^ 70 +
          1833029066268827988829916486220567352979013803703940891280562189537841) * 10 ^ 70 +
          2829930003575542875442208030946687430741624261009576435212162016706397)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 208,
    recurrence4A4Square.coeff x * exceptional4.coeff (207 - x)) = _
  rw [show 208 = 194 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_207_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_208_prefix_zero :
    (∑ x ∈ Finset.range 195,
      recurrence4A4Square.coeff x * exceptional4.coeff (208 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (208 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_208 :
    recurrence4ExceptionalProduct.coeff 208 =
      (
        -(((2725641253792193274182620206055354243613622254310452728219279 * 10 ^ 70 +
          9211046320387027331229317987424429154978899582801913020548356248387647) * 10 ^ 70 +
          0659639714033889782814072395550657284650284919492756301113498056025848)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 209,
    recurrence4A4Square.coeff x * exceptional4.coeff (208 - x)) = _
  rw [show 209 = 195 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_208_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_209_prefix_zero :
    (∑ x ∈ Finset.range 196,
      recurrence4A4Square.coeff x * exceptional4.coeff (209 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (209 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_209 :
    recurrence4ExceptionalProduct.coeff 209 =
      (
        (((2047475283930060853142452720554756053657792107378491237713831 * 10 ^ 70 +
          0736940699913991339470711104218427148761959521425964197149664685498868) * 10 ^ 70 +
          5979852913899949684851634181930296705863780662168179593069543407734376)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 210,
    recurrence4A4Square.coeff x * exceptional4.coeff (209 - x)) = _
  rw [show 210 = 196 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_209_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_210_prefix_zero :
    (∑ x ∈ Finset.range 197,
      recurrence4A4Square.coeff x * exceptional4.coeff (210 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (210 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_210 :
    recurrence4ExceptionalProduct.coeff 210 =
      (
        -(((1511012377868477209980778218210546943732865359134615602749197 * 10 ^ 70 +
          3439013368108414502687489510384711094661334306355219789347161650011717) * 10 ^ 70 +
          3341963427274117095312333538653886939135212306218704422330136481473332)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 211,
    recurrence4A4Square.coeff x * exceptional4.coeff (210 - x)) = _
  rw [show 211 = 197 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_210_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_211_prefix_zero :
    (∑ x ∈ Finset.range 198,
      recurrence4A4Square.coeff x * exceptional4.coeff (211 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (211 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_211 :
    recurrence4ExceptionalProduct.coeff 211 =
      (
        (((1095471263555622380502223757748790807203801627735360205639727 * 10 ^ 70 +
          0918872633684367436108042219080676720185699390545893194552101832154264) * 10 ^ 70 +
          8022291640047945680414486822379202756184349841035879758301812148357834)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 212,
    recurrence4A4Square.coeff x * exceptional4.coeff (211 - x)) = _
  rw [show 212 = 198 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_211_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_212_prefix_zero :
    (∑ x ∈ Finset.range 199,
      recurrence4A4Square.coeff x * exceptional4.coeff (212 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (212 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_212 :
    recurrence4ExceptionalProduct.coeff 212 =
      (
        -(((60014709644848067073681363046257013250804636822949482004011 * 10 ^ 70 +
          2107465899744441165379515974013529551917078665361953648502786842519880) * 10 ^ 70 +
          4204152096011400997454332621403902582445537974381548435970815088641522)) /
        (1785787687194522429613 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 213,
    recurrence4A4Square.coeff x * exceptional4.coeff (212 - x)) = _
  rw [show 213 = 199 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_212_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_213_prefix_zero :
    (∑ x ∈ Finset.range 200,
      recurrence4A4Square.coeff x * exceptional4.coeff (213 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (213 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_213 :
    recurrence4ExceptionalProduct.coeff 213 =
      (
        (((545821941782710222227345087526033394148081405245174259442533 * 10 ^ 70 +
          1302899478497210441759361789334541807923324950254589306527724559303996) * 10 ^ 70 +
          6850101475329406463292402972596103466002856125249658471383239448729458)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 214,
    recurrence4A4Square.coeff x * exceptional4.coeff (213 - x)) = _
  rw [show 214 = 200 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_213_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_214_prefix_zero :
    (∑ x ∈ Finset.range 201,
      recurrence4A4Square.coeff x * exceptional4.coeff (214 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (214 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_214 :
    recurrence4ExceptionalProduct.coeff 214 =
      (
        -(((375087675854711246146491786661306421588206608810630968272823 * 10 ^ 70 +
          2916617938924173261911290664106504321924524890266110431865564084428892) * 10 ^ 70 +
          0806867851592822444464040308259352433777881058501866261310251628553584)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 215,
    recurrence4A4Square.coeff x * exceptional4.coeff (214 - x)) = _
  rw [show 215 = 201 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_214_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_215_prefix_zero :
    (∑ x ∈ Finset.range 202,
      recurrence4A4Square.coeff x * exceptional4.coeff (215 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (215 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_215 :
    recurrence4ExceptionalProduct.coeff 215 =
      (
        (((253179053962105329677181757445093967527931879799282588703640 * 10 ^ 70 +
          3697393362359046737157986691512509383717340708444219183115367169802895) * 10 ^ 70 +
          2473552302411527519894999457011684705349707514328082766176599444184388)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 216,
    recurrence4A4Square.coeff x * exceptional4.coeff (215 - x)) = _
  rw [show 216 = 202 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_215_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_216_prefix_zero :
    (∑ x ∈ Finset.range 203,
      recurrence4A4Square.coeff x * exceptional4.coeff (216 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (216 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_216 :
    recurrence4ExceptionalProduct.coeff 216 =
      (
        -(((167848131588089149706577214535641429326378655324956409044289 * 10 ^ 70 +
          8756127670438514767904171629300578570972721169323840638778100606413626) * 10 ^ 70 +
          8877113674301373866070519931149170331139889027639703455876935909732054)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 217,
    recurrence4A4Square.coeff x * exceptional4.coeff (216 - x)) = _
  rw [show 217 = 203 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_216_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_217_prefix_zero :
    (∑ x ∈ Finset.range 204,
      recurrence4A4Square.coeff x * exceptional4.coeff (217 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (217 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_217 :
    recurrence4ExceptionalProduct.coeff 217 =
      (
        (((109289618079557368792602282948007232929525432345585278307674 * 10 ^ 70 +
          5598783927420380865294890683423784609129027577952380504001346798511416) * 10 ^ 70 +
          5677074932403223137752032451364361960165298675598001085704116662215832)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 218,
    recurrence4A4Square.coeff x * exceptional4.coeff (217 - x)) = _
  rw [show 218 = 204 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_217_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
