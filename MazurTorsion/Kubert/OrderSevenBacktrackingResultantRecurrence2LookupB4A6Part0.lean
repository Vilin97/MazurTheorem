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

theorem recurrence2B4A6_coeff_0 :
    recurrence2B4A6.coeff 0 =
      (0 : ℚ) := by
  unfold recurrence2B4A6
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

theorem recurrence2B4A6_coeff_1 :
    recurrence2B4A6.coeff 1 =
      (295728 : ℚ) := by
  unfold recurrence2B4A6
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

theorem recurrence2B4A6_coeff_2 :
    recurrence2B4A6.coeff 2 =
      (-48295795824 : ℚ) := by
  unfold recurrence2B4A6
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

theorem recurrence2B4A6_coeff_3 :
    recurrence2B4A6.coeff 3 =
      (11380898154160 : ℚ) := by
  unfold recurrence2B4A6
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

theorem recurrence2B4A6_coeff_4 :
    recurrence2B4A6.coeff 4 =
      (21598233311031824 : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 5 = 0 +
    5 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 5 = 5 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_5 :
    recurrence2B4A6.coeff 5 =
      (-41194443091183345662 : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 6 = 0 +
    6 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 6 = 6 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_6 :
    recurrence2B4A6.coeff 6 =
      (53663840590700019297070 : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 7 = 0 +
    7 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_7 :
    recurrence2B4A6.coeff 7 =
      (-23201524811652649489317600 : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 8 = 0 +
    8 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 8 = 8 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_8 :
    recurrence2B4A6.coeff 8 =
      (6098384957416218257344594398 : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 9 = 0 +
    9 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 9 = 9 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_9 :
    recurrence2B4A6.coeff 9 =
      (-967953883078739939065921892155 : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 10 = 0 +
    10 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 10 = 10 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_10 :
    recurrence2B4A6.coeff 10 =
      (82892725783670667050666120873497 : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 11 = 0 +
    11 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 11 = 11 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_11 :
    recurrence2B4A6.coeff 11 =
      (-1856144981353864917369446457650050 : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 12 = 0 +
    12 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 12 = 12 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_12 :
    recurrence2B4A6.coeff 12 =
      (-418701722368172578450414016960435205 : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 13 = 0 +
    13 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_13 :
    recurrence2B4A6.coeff 13 =
      (53611332834662267149424948994957601241 : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 14 = 0 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_14 :
    recurrence2B4A6.coeff 14 =
      (-3185093436539119316315991098271185135461 : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 15 = 0 +
    15 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_15 :
    recurrence2B4A6.coeff 15 =
      (112451180904710347015447621732166949269575 : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 16 = 0 +
    16 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 16 = 16 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_16 :
    recurrence2B4A6.coeff 16 =
      (-2536287263410646068245888271242111311817062 : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 17 = 0 +
    17 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_17 :
    recurrence2B4A6.coeff 17 =
      (15464610791107382615882761952051314700221623 : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 18 = 0 +
    18 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_18 :
    recurrence2B4A6.coeff 18 =
      (5041024901670907908739882386076868523552568090 : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 19 = 0 +
    19 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_19 :
    recurrence2B4A6.coeff 19 =
      (-514545343892590812237813661860878863893958931013 : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 20 = 0 +
    20 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 20 = 20 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_20 :
    recurrence2B4A6.coeff 20 =
      (26135766769116887304174423662302095000898932627535 : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 21 = 0 +
    21 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_21 :
    recurrence2B4A6.coeff 21 =
      (-713975941654232862247491182844984579150037390972059 : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 22 = 0 +
    22 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 22 = 22 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_22 :
    recurrence2B4A6.coeff 22 =
      (6364516141121975508613822390095566667933740711341968 : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 23 = 0 +
    23 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_23 :
    recurrence2B4A6.coeff 23 =
      (211606907927080171452140608897258356426137927726270856 : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 24 = 0 +
    24 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 24 = 24 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_24 :
    recurrence2B4A6.coeff 24 =
      (-5726442534940814527079383005217419683906698480954774156 : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 25 = 0 +
    25 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_25 :
    recurrence2B4A6.coeff 25 =
      (-110654624884211810069518631625534659370814452741843849159 : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 26 = 0 +
    26 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 26 = 26 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_26 :
    recurrence2B4A6.coeff 26 =
      (9688211259847801047412255167794589521267234038737742147557 : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 27 = 0 +
    27 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_27 :
    recurrence2B4A6.coeff 27 =
      (-293939945456433595613613137081695957143817080647288067092396 : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 28 = 0 +
    28 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 28 = 28 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_28 :
    recurrence2B4A6.coeff 28 =
      (5893091686577840561127797707023068209825249876914095050328484 : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 29 = 0 +
    29 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 29 = 29 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_29 :
    recurrence2B4A6.coeff 29 =
      (-97012077887686224003577964860533861189828907690353098810986885 : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 30 = 0 +
    30 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 30 = 30 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_30 :
    recurrence2B4A6.coeff 30 =
      (1584039089259065660967448053901442453566192953046119703156479092 : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 31 = 0 +
    31 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 31 = 31 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_31 :
    recurrence2B4A6.coeff 31 =
      (-26680850485154536731846652686473466498860477993982791939292269636 : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 32 = 0 +
    32 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_32 :
    recurrence2B4A6.coeff 32 =
      (393937779483486943736014890483418792425527482303210872400867641202 : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 33 = 0 +
    33 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 33 = 32 +
      1 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 1 = 1 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_33 :
    recurrence2B4A6.coeff 33 =
      (-3926449751156599965407807304831634326923457929780200060774221978630 : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 34 = 0 +
    34 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 34 = 32 +
      2 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 2 = 2 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_34 :
    recurrence2B4A6.coeff 34 =
      (3089325876132521739556067881023944132187159886464478242182263545851 : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 35 = 0 +
    35 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_35 :
    recurrence2B4A6.coeff 35 =
      (860324505091281878683508810819303258149306430595689417024321225655268 : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 36 = 0 +
    36 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 36 = 32 +
      4 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_36 :
    recurrence2B4A6.coeff 36 =
      -((2 * 10 ^ 70 +
        2799397858270844487058443609146349430045707223163289756417522725013962) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 37 = 0 +
    37 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 37 = 32 +
      5 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 5 = 5 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_37 :
    recurrence2B4A6.coeff 37 =
      ((41 * 10 ^ 70 +
        2242881961742226547995794359975724593305217207610837303130504233105905) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 38 = 0 +
    38 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 38 = 32 +
      6 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 6 = 6 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_38 :
    recurrence2B4A6.coeff 38 =
      -((629 * 10 ^ 70 +
        6184155950720443271770505796746843230518910392448592222420320574362853) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 39 = 0 +
    39 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 39 = 32 +
      7 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_39 :
    recurrence2B4A6.coeff 39 =
      ((8667 * 10 ^ 70 +
        8251042864695491368250257557711508754581580301680174604782554788184390) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 40 = 0 +
    40 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 40 = 32 +
      8 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 8 = 8 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_40 :
    recurrence2B4A6.coeff 40 =
      -((108874 * 10 ^ 70 +
        7370810659229774481908346542081046482383265783613196278293657588556749) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 41 = 0 +
    41 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 41 = 32 +
      9 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 9 = 9 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_41 :
    recurrence2B4A6.coeff 41 =
      ((1241927 * 10 ^ 70 +
        7973259527099598261338955714172557095541836132167726741383418848106750) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 42 = 0 +
    42 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 42 = 32 +
      10 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 10 = 10 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_42 :
    recurrence2B4A6.coeff 42 =
      -((12865757 * 10 ^ 70 +
        7721239414684442454660171834934652366231794121689630685353983586296209) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 43 = 0 +
    43 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 43 = 32 +
      11 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 11 = 11 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_43 :
    recurrence2B4A6.coeff 43 =
      ((122356386 * 10 ^ 70 +
        2090247725801623005294125394712216025673987307507814678026343351117576) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 44 = 0 +
    44 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 44 = 32 +
      12 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 12 = 12 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_44 :
    recurrence2B4A6.coeff 44 =
      -((1085302177 * 10 ^ 70 +
        0063430485144682885490348489986098615883508380234307859241339807723043) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 45 = 0 +
    45 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_45 :
    recurrence2B4A6.coeff 45 =
      ((9072560584 * 10 ^ 70 +
        8597391108321619552676219120839218295243529026565019007124345114018226) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 46 = 0 +
    46 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 46 = 32 +
      14 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_46 :
    recurrence2B4A6.coeff 46 =
      -((71417844344 * 10 ^ 70 +
        5835489196391255323745921427788325602388782404494510781704101443492398) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 47 = 0 +
    47 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 47 = 32 +
      15 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_47 :
    recurrence2B4A6.coeff 47 =
      ((525513909879 * 10 ^ 70 +
        4378660265969109729680764698281784187784728660960962677841329613043670) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 48 = 0 +
    48 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 48 = 32 +
      16 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 16 = 16 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_48 :
    recurrence2B4A6.coeff 48 =
      -((3600763800428 * 10 ^ 70 +
        7438602102700346942624773929516319985308690755053007655162361253183451) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 49 = 0 +
    49 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_49 :
    recurrence2B4A6.coeff 49 =
      ((23103734982856 * 10 ^ 70 +
        2817806246617596524784561521306848041181672740722565509695052902074401) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 50 = 0 +
    50 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_50 :
    recurrence2B4A6.coeff 50 =
      -((140520440861794 * 10 ^ 70 +
        3319987983862194669949699332810436335745672530270690034934535187610322) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 51 = 0 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_51 :
    recurrence2B4A6.coeff 51 =
      ((817174537752128 * 10 ^ 70 +
        6497546327858875879410202282329090289995185331786819647423456095298515) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 52 = 0 +
    52 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 52 = 32 +
      20 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 20 = 20 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_52 :
    recurrence2B4A6.coeff 52 =
      -((4525639111771692 * 10 ^ 70 +
        6872406728001613611727152803169700532861403666625708758609607211234438) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 53 = 0 +
    53 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_53 :
    recurrence2B4A6.coeff 53 =
      ((23505188955751254 * 10 ^ 70 +
        3611451464977859484497198525337474278982700599169984985621445467797302) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 54 = 0 +
    54 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 22 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_54 :
    recurrence2B4A6.coeff 54 =
      -((112774123996845342 * 10 ^ 70 +
        1043927183275366996227370211576402007123576507730529289181129147900351) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 55 = 0 +
    55 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_55 :
    recurrence2B4A6.coeff 55 =
      ((500629990657554129 * 10 ^ 70 +
        8038268813136479582166895581089241230386899823743523527016427443305263) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 56 = 0 +
    56 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 56 = 32 +
      24 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 24 = 24 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_56 :
    recurrence2B4A6.coeff 56 =
      -((2126742139868856210 * 10 ^ 70 +
        3550027762967170800824148945422387610020451569185202057922674656290636) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 57 = 0 +
    57 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_57 :
    recurrence2B4A6.coeff 57 =
      ((9126029833500678955 * 10 ^ 70 +
        5765451004936134831494805217748463932515677136123577672357356176692013) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 58 = 0 +
    58 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 26 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_58 :
    recurrence2B4A6.coeff 58 =
      -((39557438081517777246 * 10 ^ 70 +
        0335160837136247849721560610895067515364918785462236216089039368754825) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 59 = 0 +
    59 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_59 :
    recurrence2B4A6.coeff 59 =
      ((154286354705978429373 * 10 ^ 70 +
        2887607242931700339502122418500673163430437506706198559786979669172681) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 60 = 0 +
    60 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 60 = 32 +
      28 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 28 = 28 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_60 :
    recurrence2B4A6.coeff 60 =
      -((436686485481088901672 * 10 ^ 70 +
        6058203440820528492598879993294272877811894946865626095699649873859017) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 61 = 0 +
    61 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 61 = 32 +
      29 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 29 = 29 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_61 :
    recurrence2B4A6.coeff 61 =
      ((545579647747844217739 * 10 ^ 70 +
        7084788746906813391362741216768202785835537843135968054717230762667949) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 62 = 0 +
    62 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 62 = 32 +
      30 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 30 = 30 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_62 :
    recurrence2B4A6.coeff 62 =
      ((262691054373412947278 * 10 ^ 70 +
        3527379802046587344343518720309071519336679647729606033811913335217431) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 63 = 0 +
    63 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 31 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_63 :
    recurrence2B4A6.coeff 63 =
      ((12792376864242954440474 * 10 ^ 70 +
        9452452838425535214234968302015243037054807521218127728636369566307643) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 64 = 0 +
    64 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_64 :
    recurrence2B4A6.coeff 64 =
      -((142909730821755173766422 * 10 ^ 70 +
        7645808963798339918623537521150685340404843757728746958176308606589110) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 65 = 0 +
    65 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 65 = 32 +
      33 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 33 = 32 +
      1 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 1 = 1 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_65 :
    recurrence2B4A6.coeff 65 =
      ((498767023213036882633033 * 10 ^ 70 +
        6882757081864799127589947339284825600071445499258515029410219676825347) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 66 = 0 +
    66 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 66 = 32 +
      34 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 34 = 32 +
      2 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 2 = 2 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_66 :
    recurrence2B4A6.coeff 66 =
      ((785795622913982209925333 * 10 ^ 70 +
        3686207655711903207291297524110070389724972072911605091031805580731064) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 67 = 0 +
    67 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_67 :
    recurrence2B4A6.coeff 67 =
      -((13699759313921626456394043 * 10 ^ 70 +
        1026631486277096696901218333041267273719256404261638721988837159136731) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 68 = 0 +
    68 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 68 = 32 +
      36 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 36 = 32 +
      4 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_68 :
    recurrence2B4A6.coeff 68 =
      ((44977805553541830882610995 * 10 ^ 70 +
        3735758806983638212564946345314201472704865225974512091769294834517535) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 69 = 0 +
    69 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 32 +
      5 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 5 = 5 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_69 :
    recurrence2B4A6.coeff 69 =
      ((30213848453671358819491298 * 10 ^ 70 +
        2594217574227325791657856307298337710262109383948444249126973026548776) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 70 = 0 +
    70 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 70 = 32 +
      38 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 38 = 32 +
      6 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 6 = 6 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_70 :
    recurrence2B4A6.coeff 70 =
      -((747472894894980569019983906 * 10 ^ 70 +
        4740409312617299556398216428234550806606266236288138943739096948077154) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 71 = 0 +
    71 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 71 = 32 +
      39 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 39 = 32 +
      7 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_71 :
    recurrence2B4A6.coeff 71 =
      ((2932628451714858762804814554 * 10 ^ 70 +
        3284151188594087695780838887909524366059881296754919882291415374285531) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 72 = 0 +
    72 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 72 = 32 +
      40 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 40 = 32 +
      8 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 8 = 8 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_72 :
    recurrence2B4A6.coeff 72 =
      -((6785287170195378224069793135 * 10 ^ 70 +
        1726927665929918630687757484075108146734378295568958197639315073063262) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 73 = 0 +
    73 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 73 = 32 +
      41 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 41 = 32 +
      9 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 9 = 9 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_73 :
    recurrence2B4A6.coeff 73 =
      -((2738509023999403695534031985 * 10 ^ 70 +
        7514172592205333805006851391743571001871224453070120210618008290662677) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 74 = 0 +
    74 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 74 = 32 +
      42 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 42 = 32 +
      10 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 10 = 10 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_74 :
    recurrence2B4A6.coeff 74 =
      ((249560477544070574237608388252 * 10 ^ 70 +
        5986627043733134479214682116033842626560540874832081513847603470783215) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 75 = 0 +
    75 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 75 = 32 +
      43 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 43 = 32 +
      11 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 11 = 11 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_75 :
    recurrence2B4A6.coeff 75 =
      -((1916709751470019726696406990424 * 10 ^ 70 +
        7196854050999853931431949317757255516517708802685453642259833509507164) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 76 = 0 +
    76 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 76 = 32 +
      44 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 44 = 32 +
      12 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 12 = 12 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_76 :
    recurrence2B4A6.coeff 76 =
      ((4828230528881993466518401307409 * 10 ^ 70 +
        9505470983133813108496416479311754814567826771653886069672444301005854) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 77 = 0 +
    77 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 77 = 32 +
      45 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_77 :
    recurrence2B4A6.coeff 77 =
      ((23519749310731000592021220841822 * 10 ^ 70 +
        4106484428518246456663636453781330157683206343758917925538538532577454) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 78 = 0 +
    78 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 78 = 32 +
      46 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 46 = 32 +
      14 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_78 :
    recurrence2B4A6.coeff 78 =
      -((225344506257172816340046025854638 * 10 ^ 70 +
        2190142372721398959335885529037527379490930297072153656899159352760023) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 79 = 0 +
    79 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 79 = 32 +
      47 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 47 = 32 +
      15 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_79 :
    recurrence2B4A6.coeff 79 =
      ((518670615659708372924880108339835 * 10 ^ 70 +
        3833369443583498217991503771490694716694410333730356832907334883547337) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 80 = 0 +
    80 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 80 = 32 +
      48 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 48 = 32 +
      16 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 16 = 16 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_80 :
    recurrence2B4A6.coeff 80 =
      ((2069266604077174817655299808944178 * 10 ^ 70 +
        1964404323376386679350658336460211554345438723053151489570221632885969) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 81 = 0 +
    81 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_81 :
    recurrence2B4A6.coeff 81 =
      -((16864867846872618670090197051940232 * 10 ^ 70 +
        5618942971528122126822783362016835640174693954867670488088267075997186) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 82 = 0 +
    82 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_82 :
    recurrence2B4A6.coeff 82 =
      ((28331904815606710647614414477111370 * 10 ^ 70 +
        5625444480584716318233455109660116683979256979599477377170140257172667) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 83 = 0 +
    83 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_83 :
    recurrence2B4A6.coeff 83 =
      ((150740363344684817034991380065717440 * 10 ^ 70 +
        9808400276021747393499444915917080159992005142423207162987092745519673) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 84 = 0 +
    84 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 84 = 32 +
      52 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 52 = 32 +
      20 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 20 = 20 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_84 :
    recurrence2B4A6.coeff 84 =
      -((855757421945388756733040797839952951 * 10 ^ 70 +
        4304672364506487668050031126830524690564204820642432841985641377453282) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 85 = 0 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_85 :
    recurrence2B4A6.coeff 85 =
      ((491481778600053349061153605587800743 * 10 ^ 70 +
        4449669442316463206375760096652164439639035010082703788748223971928245) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 86 = 0 +
    86 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 22 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_86 :
    recurrence2B4A6.coeff 86 =
      ((9497343440883987218903146892122662845 * 10 ^ 70 +
        3986295753714733239135781766695468381494173450845389566808587132691167) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 87 = 0 +
    87 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_87 :
    recurrence2B4A6.coeff 87 =
      -((29157942109679306806608973608780490376 * 10 ^ 70 +
        1877825311225945931567441904073338646737130929696608434293956427625564) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 88 = 0 +
    88 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 88 = 32 +
      56 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 56 = 32 +
      24 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 24 = 24 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_88 :
    recurrence2B4A6.coeff 88 =
      -((57501949268763857598733470289844671022 * 10 ^ 70 +
        6665608527798553671387130488376103174120094182038026714964266326310114) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 89 = 0 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_89 :
    recurrence2B4A6.coeff 89 =
      ((548786269470432385451233403232636596123 * 10 ^ 70 +
        1162876867326974816952916190144472442252073198924152500709442875555951) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 90 = 0 +
    90 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 26 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_90 :
    recurrence2B4A6.coeff 90 =
      -((626591355730027641659098108204590279779 * 10 ^ 70 +
        3466297668747282286621774548873636048027372138309053219606337888102621) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 91 = 0 +
    91 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 91 = 32 +
      59 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_91 :
    recurrence2B4A6.coeff 91 =
      -((6223531260094756896647297251109688446350 * 10 ^ 70 +
        2156345435574995796501469790282090709770778311125594020101739521198250) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 92 = 0 +
    92 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 92 = 32 +
      60 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 60 = 32 +
      28 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 28 = 28 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_92 :
    recurrence2B4A6.coeff 92 =
      ((28511152883231126187190207407854396899129 * 10 ^ 70 +
        5539522100451039915601520146055505632787040435695348156916556340867000) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 93 = 0 +
    93 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 93 = 32 +
      61 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 61 = 32 +
      29 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 29 = 29 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_93 :
    recurrence2B4A6.coeff 93 =
      -((7302393996706513440756597861882250478873 * 10 ^ 70 +
        2695120974098481996719612738223889394070725340541250821256749223135699) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 94 = 0 +
    94 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 94 = 32 +
      62 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 62 = 32 +
      30 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 30 = 30 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_94 :
    recurrence2B4A6.coeff 94 =
      -((349162565332286461443857099414542656095823 * 10 ^ 70 +
        1986923808776978729755371474770291345333088217512462919215531890949087) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 95 = 0 +
    95 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 31 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2B4A6_coeff_95 :
    recurrence2B4A6.coeff 95 =
      ((1252333982703520639331779985691691500533862 * 10 ^ 70 +
        0497270855858671983826415451364611751931853073645351340248633878274692) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 96 = 0 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_96_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (96 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B4A6_coeff_96 :
    recurrence2B4A6.coeff 96 =
      -((4091006489272142110232111228995174235196 * 10 ^ 70 +
        7628156919512961119702734456871355529604284933674716934484419967504009) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 97 = 1 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_96_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_97_prefix_zero :
    (∑ x ∈ Finset.range 2,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (97 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (97 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B4A6_coeff_97 :
    recurrence2B4A6.coeff 97 =
      -((14208516035599124162632954863327328301529827 * 10 ^ 70 +
        7547034064733587888352382837699780153011597510224976876478359163224756) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 98 = 2 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_97_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_98_prefix_zero :
    (∑ x ∈ Finset.range 3,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (98 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (98 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B4A6_coeff_98 :
    recurrence2B4A6.coeff 98 =
      ((46273581685451388067239302181670332683039091 * 10 ^ 70 +
        8984471049490948887230041776455879404025110694221476583470365202160248) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 99 = 3 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_98_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_99_prefix_zero :
    (∑ x ∈ Finset.range 4,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (99 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (99 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B4A6_coeff_99 :
    recurrence2B4A6.coeff 99 =
      ((936442084416790838860116518933150802277568 * 10 ^ 70 +
        3984689653217668425498184960561650791407984482168574932631558621354891) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 100 = 4 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_99_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_100_prefix_zero :
    (∑ x ∈ Finset.range 5,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (100 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (100 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B4A6_coeff_100 :
    recurrence2B4A6.coeff 100 =
      -((480206722237731905778177035325657916000444510 * 10 ^ 70 +
        4458462757423212045183062186924149434377166727694156664369342800715543) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 101 = 5 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_100_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_101_prefix_zero :
    (∑ x ∈ Finset.range 6,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (101 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (101 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B4A6_coeff_101 :
    recurrence2B4A6.coeff 101 =
      ((1541836724068147627997844549260490258959164544 * 10 ^ 70 +
        9223331678857781731647579538126954512039641331449874329043589599310774) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 102 = 6 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_101_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_102_prefix_zero :
    (∑ x ∈ Finset.range 7,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (102 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (102 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B4A6_coeff_102 :
    recurrence2B4A6.coeff 102 =
      -((283187357193795881091752199314032986328824892 * 10 ^ 70 +
        6877342002341374026755746935446261402917778582639989942386565374782883) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 103 = 7 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_102_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_103_prefix_zero :
    (∑ x ∈ Finset.range 8,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (103 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (103 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B4A6_coeff_103 :
    recurrence2B4A6.coeff 103 =
      -((13869751646016820276979631724657316459889086206 * 10 ^ 70 +
        8781517271466444166627934652293443149487788232072960633427778766601340) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 104 = 8 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_103_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_104_prefix_zero :
    (∑ x ∈ Finset.range 9,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (104 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (104 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B4A6_coeff_104 :
    recurrence2B4A6.coeff 104 =
      ((48237594011882485375717821931071921228776330989 * 10 ^ 70 +
        2325103756826172327442481741918590598718016450535770935302113712381663) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 105 = 9 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_104_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_105_prefix_zero :
    (∑ x ∈ Finset.range 10,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (105 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (105 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B4A6_coeff_105 :
    recurrence2B4A6.coeff 105 =
      -((33237380507910022865996851526963937409186781731 * 10 ^ 70 +
        4309823830773572348052542065124818459790833219327894107446805744346553) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 106 = 10 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_105_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_106_prefix_zero :
    (∑ x ∈ Finset.range 11,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (106 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (106 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B4A6_coeff_106 :
    recurrence2B4A6.coeff 106 =
      -((316446014474861743030751793998826600879539047875 * 10 ^ 70 +
        5319500907515132362019470633999636601219141441946665917162654992806116) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 107 = 11 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_106_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_107_prefix_zero :
    (∑ x ∈ Finset.range 12,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (107 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (107 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B4A6_coeff_107 :
    recurrence2B4A6.coeff 107 =
      ((1341622699958988104215666394285125004556735049004 * 10 ^ 70 +
        1699497549605809592884784563747584308421619590418741429695713164926285) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 108 = 12 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_107_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_108_prefix_zero :
    (∑ x ∈ Finset.range 13,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (108 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (108 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B4A6_coeff_108 :
    recurrence2B4A6.coeff 108 =
      -((1849653720704085674789149527146714113213758799258 * 10 ^ 70 +
        6776875915483198623192674206936156618744717365160602975763070461026087) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 109 = 13 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_108_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_109_prefix_zero :
    (∑ x ∈ Finset.range 14,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (109 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (109 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B4A6_coeff_109 :
    recurrence2B4A6.coeff 109 =
      -((4665790845714757253314670025778807758023528653320 * 10 ^ 70 +
        2657515607950682379196824298674573563384047202715554284814597785408980) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 110 = 14 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_109_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_110_prefix_zero :
    (∑ x ∈ Finset.range 15,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (110 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (110 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B4A6_coeff_110 :
    recurrence2B4A6.coeff 110 =
      ((30263288033908214649740984042162215887944201460072 * 10 ^ 70 +
        1396844241734397174543869788212977879419890285361178578725120958347289) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 111 = 15 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_110_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_111_prefix_zero :
    (∑ x ∈ Finset.range 16,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (111 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (111 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B4A6_coeff_111 :
    recurrence2B4A6.coeff 111 =
      -((66431252268844708278058708078653744674956726013624 * 10 ^ 70 +
        8711695676496518092629605207485632222889213912008420750494098702106245) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 112 = 16 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_111_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_112_prefix_zero :
    (∑ x ∈ Finset.range 17,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (112 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (112 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B4A6_coeff_112 :
    recurrence2B4A6.coeff 112 =
      -((58043069279496532433944186290514076430532774629 * 10 ^ 70 +
        9972001319498707490447403688301253991491757320082641533403106526800802) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 113 = 17 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_112_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_113_prefix_zero :
    (∑ x ∈ Finset.range 18,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (113 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (113 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B4A6_coeff_113 :
    recurrence2B4A6.coeff 113 =
      ((479291015088781095543929569547729210354963882557689 * 10 ^ 70 +
        5732730600346603837749591729511294524414604480078883090172912989561740) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 114 = 18 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_113_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_114_prefix_zero :
    (∑ x ∈ Finset.range 19,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (114 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (114 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B4A6_coeff_114 :
    recurrence2B4A6.coeff 114 =
      -((1628152787962784808597520191863964245821143599234050 * 10 ^ 70 +
        1883442827068387652679944760238308837075600445717992172110672936688663) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 115 = 19 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_114_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_115_prefix_zero :
    (∑ x ∈ Finset.range 20,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (115 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (115 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B4A6_coeff_115 :
    recurrence2B4A6.coeff 115 =
      ((2286124645237824962292926193822128769763450740521096 * 10 ^ 70 +
        1290737863323534318943876931785701493293448054328158791329981081175317) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 116 = 20 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_115_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_116_prefix_zero :
    (∑ x ∈ Finset.range 21,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (116 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (116 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B4A6_coeff_116 :
    recurrence2B4A6.coeff 116 =
      ((2938713030256383452097861961693993582164588507756100 * 10 ^ 70 +
        6264064713298302647500430428343391385839822165433854360831147898570123) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 117 = 21 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_116_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_117_prefix_zero :
    (∑ x ∈ Finset.range 22,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (117 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (117 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B4A6_coeff_117 :
    recurrence2B4A6.coeff 117 =
      -((24661809258350110407640602365997854601208123035110356 * 10 ^ 70 +
        5488671716698842513779369432361343402527343446865557195292641177432461) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 118 = 22 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_117_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_118_prefix_zero :
    (∑ x ∈ Finset.range 23,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (118 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (118 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B4A6_coeff_118 :
    recurrence2B4A6.coeff 118 =
      ((66137808891070856570939241102379885385255787474084119 * 10 ^ 70 +
        1331078411765369141580882332823443916012479762231743690670814754312867) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 119 = 23 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_118_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_119_prefix_zero :
    (∑ x ∈ Finset.range 24,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (119 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (119 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B4A6_coeff_119 :
    recurrence2B4A6.coeff 119 =
      -((78253973920687122587679791955631066874300210382208583 * 10 ^ 70 +
        6161866050575282623357054977902513285757547038305755538489146338171345) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 120 = 24 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_119_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_120_prefix_zero :
    (∑ x ∈ Finset.range 25,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (120 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (120 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B4A6_coeff_120 :
    recurrence2B4A6.coeff 120 =
      -((116899185588875985526674703988212017820232390778764557 * 10 ^ 70 +
        4341500338443759490739938370214968119072242076685145032073472440623533) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 121 = 25 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_120_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_121_prefix_zero :
    (∑ x ∈ Finset.range 26,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (121 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (121 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B4A6_coeff_121 :
    recurrence2B4A6.coeff 121 =
      ((841955462512583362077249673905653553001679923716591338 * 10 ^ 70 +
        4740526859466181092899640203803515655371934741722112776318425651837134) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 122 = 26 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_121_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_122_prefix_zero :
    (∑ x ∈ Finset.range 27,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (122 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (122 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B4A6_coeff_122 :
    recurrence2B4A6.coeff 122 =
      -((2249689796650576332954110756516242429091980206988307756 * 10 ^ 70 +
        6967653556960327977660064785061271894833614993916396696653433022937152) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 123 = 27 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_122_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_123_prefix_zero :
    (∑ x ∈ Finset.range 28,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (123 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (123 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B4A6_coeff_123 :
    recurrence2B4A6.coeff 123 =
      ((3272856280808246190816976947937703604934841554956323057 * 10 ^ 70 +
        5862945219945461792661848404335571267586144781285710385089600733381095) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 124 = 28 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_123_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_124_prefix_zero :
    (∑ x ∈ Finset.range 29,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (124 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (124 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B4A6_coeff_124 :
    recurrence2B4A6.coeff 124 =
      ((247617301164659908992288030994746537477318538834656114 * 10 ^ 70 +
        6820615750080845004517966552928366920087636915339435163210189668850096) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 125 = 29 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_124_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_125_prefix_zero :
    (∑ x ∈ Finset.range 30,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (125 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (125 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B4A6_coeff_125 :
    recurrence2B4A6.coeff 125 =
      -((16938217750021426737492787501831237387116356384461482995 * 10 ^ 70 +
        1283103108429710964252476739734658333160511239423790322515791473552252) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 126 = 30 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_125_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_126_prefix_zero :
    (∑ x ∈ Finset.range 31,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (126 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (126 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B4A6_coeff_126 :
    recurrence2B4A6.coeff 126 =
      ((56687677161632542737863572565711410550741951525974646743 * 10 ^ 70 +
        6624360989859245869469486616201446495867218575217264678303268896079362) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 127 = 31 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_126_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_127_prefix_zero :
    (∑ x ∈ Finset.range 32,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (127 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (127 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B4A6_coeff_127 :
    recurrence2B4A6.coeff 127 =
      -((115896538163683368182430900256094045667024723932690450859 * 10 ^ 70 +
        3386278479460963919866011847844028175911135739374241402497224565276687) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 128 = 32 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_127_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_128_prefix_zero :
    (∑ x ∈ Finset.range 33,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (128 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (128 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B4A6_coeff_128 :
    recurrence2B4A6.coeff 128 =
      ((145096836085661228127510526508000167537478937867566824724 * 10 ^ 70 +
        8500726033365095712504691058326586148792141786626107064577057798460507) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 129 = 33 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_128_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_129_prefix_zero :
    (∑ x ∈ Finset.range 34,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (129 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (129 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B4A6_coeff_129 :
    recurrence2B4A6.coeff 129 =
      -((3327407575963962141784554815796641284598954399171350813 * 10 ^ 70 +
        1878012981855150046792977904267471768793557812459694094046927418795121) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 130 = 34 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_129_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_130_prefix_zero :
    (∑ x ∈ Finset.range 35,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (130 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (130 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B4A6_coeff_130 :
    recurrence2B4A6.coeff 130 =
      -((572738612237464139608726372141331893301014184606707212406 * 10 ^ 70 +
        2424326725532068131347149588026285914966692294833917370351314882510335) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 131 = 35 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_130_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_131_prefix_zero :
    (∑ x ∈ Finset.range 36,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (131 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (131 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B4A6_coeff_131 :
    recurrence2B4A6.coeff 131 =
      ((1926355789995242331041031493210298764049374098796908851363 * 10 ^ 70 +
        2876046356619050399054965727384956060545077703560427051999612114963108) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 132 = 36 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_131_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_132_prefix_zero :
    (∑ x ∈ Finset.range 37,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (132 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (132 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B4A6_coeff_132 :
    recurrence2B4A6.coeff 132 =
      -((4290698486450707061837586842325248685694971681771475880713 * 10 ^ 70 +
        3883004854067759822487939887555807937862884800097914843746871142340622) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 133 = 37 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_132_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_133_prefix_zero :
    (∑ x ∈ Finset.range 38,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (133 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (133 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B4A6_coeff_133 :
    recurrence2B4A6.coeff 133 =
      ((7409342268432273632867778666644326419204353653855750411384 * 10 ^ 70 +
        4670092978537278711400287072993435832540446906370017630884135047153656) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 134 = 38 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_133_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_134_prefix_zero :
    (∑ x ∈ Finset.range 39,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (134 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (134 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B4A6_coeff_134 :
    recurrence2B4A6.coeff 134 =
      -((10029448182175576844759189453905648682604853602538547236581 * 10 ^ 70 +
        3166450826051710194375593821258381047525261647120207445468470648948045) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 135 = 39 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_134_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_135_prefix_zero :
    (∑ x ∈ Finset.range 40,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (135 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (135 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B4A6_coeff_135 :
    recurrence2B4A6.coeff 135 =
      ((9488668145653268777547403245145464054886262039140556338586 * 10 ^ 70 +
        5127117973568357904543658306802753307115022193624411753373738907145248) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 136 = 40 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_135_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_136_prefix_zero :
    (∑ x ∈ Finset.range 41,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (136 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (136 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B4A6_coeff_136 :
    recurrence2B4A6.coeff 136 =
      -((1751256684582361390301270317327095921694012915976841197716 * 10 ^ 70 +
        2707756241334163894520927103778232000112891116387012658076862000832664) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 137 = 41 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_136_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_137_prefix_zero :
    (∑ x ∈ Finset.range 42,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (137 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (137 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B4A6_coeff_137 :
    recurrence2B4A6.coeff 137 =
      -((17762977438755128966583041210464321078210240956886453818091 * 10 ^ 70 +
        5863568144404664798879720823413660527739733667690802035806303224646173) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 138 = 42 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_137_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_138_prefix_zero :
    (∑ x ∈ Finset.range 43,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (138 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (138 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B4A6_coeff_138 :
    recurrence2B4A6.coeff 138 =
      ((52466297211583512021956729823253949825801768493286385524103 * 10 ^ 70 +
        9750695526171895792103681282954579898394809616019985071425147499193934) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 139 = 43 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_138_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_139_prefix_zero :
    (∑ x ∈ Finset.range 44,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (139 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (139 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_139_suffix_zero :
    (∑ x ∈ Finset.range 1,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (139 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_139 :
    recurrence2B4A6.coeff 139 =
      -((102385849725043060596874165671446841760423006647201650146099 * 10 ^ 70 +
        4779573053278174070169020798111416034204235558238495519466178512748318) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 140 = 44 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 31 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_139_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_139_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_140_prefix_zero :
    (∑ x ∈ Finset.range 45,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (140 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (140 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_140_suffix_zero :
    (∑ x ∈ Finset.range 2,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (140 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_140 :
    recurrence2B4A6.coeff 140 =
      ((162311373217987086600844083338047816972745225702149228632809 * 10 ^ 70 +
        8001559342729716996815057705047280952930559685509500483737428780729217) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 141 = 45 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 30 +
      2 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_140_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_140_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_141_prefix_zero :
    (∑ x ∈ Finset.range 46,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (141 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (141 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_141_suffix_zero :
    (∑ x ∈ Finset.range 3,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (141 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_141 :
    recurrence2B4A6.coeff 141 =
      -((221385396803681970442694132009581343262712117888184627931012 * 10 ^ 70 +
        7202642497553652647583211839215766186387680220306736593475631799483497) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 142 = 46 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 29 +
      3 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_141_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_141_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_142_prefix_zero :
    (∑ x ∈ Finset.range 47,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (142 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (142 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_142_suffix_zero :
    (∑ x ∈ Finset.range 4,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (142 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_142 :
    recurrence2B4A6.coeff 142 =
      ((264891143332765045421595708991625957367310060087824460499792 * 10 ^ 70 +
        9027144181679300936402599735641237506452625095654786380199814732745794) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 143 = 47 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 28 +
      4 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_142_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_142_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_143_prefix_zero :
    (∑ x ∈ Finset.range 48,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (143 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (143 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_143_suffix_zero :
    (∑ x ∈ Finset.range 5,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (143 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_143 :
    recurrence2B4A6.coeff 143 =
      -((278144444657295157814887423971666465303336857207244437882053 * 10 ^ 70 +
        9518807201812387517068825733215532167882435263085010768041029269860370) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 144 = 48 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 27 +
      5 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_143_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_143_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_144_prefix_zero :
    (∑ x ∈ Finset.range 49,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (144 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (144 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_144_suffix_zero :
    (∑ x ∈ Finset.range 6,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (144 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_144 :
    recurrence2B4A6.coeff 144 =
      ((251354075746961811485569417229410511398873056752531421694666 * 10 ^ 70 +
        1405840111140732187380137970927955351480209269493249751561306792585590) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 145 = 49 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 26 +
      6 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_144_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_144_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_145_prefix_zero :
    (∑ x ∈ Finset.range 50,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (145 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (145 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_145_suffix_zero :
    (∑ x ∈ Finset.range 7,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (145 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_145 :
    recurrence2B4A6.coeff 145 =
      -((183616099415499125271866327725354363169356592005167491831557 * 10 ^ 70 +
        1740974002875037999068996564164848299245207280431276684084278429896915) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 146 = 50 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 25 +
      7 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_145_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_145_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_146_prefix_zero :
    (∑ x ∈ Finset.range 51,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (146 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (146 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_146_suffix_zero :
    (∑ x ∈ Finset.range 8,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (146 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_146 :
    recurrence2B4A6.coeff 146 =
      ((84297208580639382260173466627945108823920617096857633005832 * 10 ^ 70 +
        5350910363761789004305619671718556344797913778788606008604181890461195) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 147 = 51 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 24 +
      8 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_146_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_146_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_147_prefix_zero :
    (∑ x ∈ Finset.range 52,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (147 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (147 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_147_suffix_zero :
    (∑ x ∈ Finset.range 9,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (147 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_147 :
    recurrence2B4A6.coeff 147 =
      ((28994877370663785501474380358496271798771498506065663036826 * 10 ^ 70 +
        5435713414812222377754890407135648391743554614005763230390321648179683) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 148 = 52 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 23 +
      9 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_147_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_147_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_148_prefix_zero :
    (∑ x ∈ Finset.range 53,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (148 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (148 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_148_suffix_zero :
    (∑ x ∈ Finset.range 10,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (148 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_148 :
    recurrence2B4A6.coeff 148 =
      -((135260200148949165665853186647744065382652272322099516090587 * 10 ^ 70 +
        0734084497299002495596708640759532519242516279198388866413394856917050) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 149 = 53 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 22 +
      10 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_148_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_148_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_149_prefix_zero :
    (∑ x ∈ Finset.range 54,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (149 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (149 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_149_suffix_zero :
    (∑ x ∈ Finset.range 11,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (149 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_149 :
    recurrence2B4A6.coeff 149 =
      ((216004807477974304310426526706881430259461929040300352231050 * 10 ^ 70 +
        6314107521278387789556342032491498751303642207499470140814495592339442) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 150 = 54 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 21 +
      11 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_149_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_149_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_150_prefix_zero :
    (∑ x ∈ Finset.range 55,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (150 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (150 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_150_suffix_zero :
    (∑ x ∈ Finset.range 12,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (150 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_150 :
    recurrence2B4A6.coeff 150 =
      -((260035568648240052822578865024593666543526046226653255065800 * 10 ^ 70 +
        8072154874487309737352478133468668039303197427806517097557124750319066) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 151 = 55 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 20 +
      12 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_150_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_150_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_151_prefix_zero :
    (∑ x ∈ Finset.range 56,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (151 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (151 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_151_suffix_zero :
    (∑ x ∈ Finset.range 13,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (151 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_151 :
    recurrence2B4A6.coeff 151 =
      ((265564916752566275636315711306033552060343160497966617200133 * 10 ^ 70 +
        7608980127655713166890608928084853134044441304428423350775142348109767) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 152 = 56 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 19 +
      13 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_151_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_151_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_152_prefix_zero :
    (∑ x ∈ Finset.range 57,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (152 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (152 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_152_suffix_zero :
    (∑ x ∈ Finset.range 14,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (152 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_152 :
    recurrence2B4A6.coeff 152 =
      -((239226374289538883599289178688455186002253477541323489741906 * 10 ^ 70 +
        9628352668151073589418245429295934358154692753361195492814579325025525) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 153 = 57 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 18 +
      14 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_152_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_152_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_153_prefix_zero :
    (∑ x ∈ Finset.range 58,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (153 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (153 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_153_suffix_zero :
    (∑ x ∈ Finset.range 15,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (153 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_153 :
    recurrence2B4A6.coeff 153 =
      ((192807974560344901344399669890589668052163052018888698365268 * 10 ^ 70 +
        5579239222870089587082064598909364200039555445374209183031306734591181) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 154 = 58 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 17 +
      15 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_153_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_153_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_154_prefix_zero :
    (∑ x ∈ Finset.range 59,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (154 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (154 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_154_suffix_zero :
    (∑ x ∈ Finset.range 16,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (154 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_154 :
    recurrence2B4A6.coeff 154 =
      -((139200832440863768258754210250756981202473928830790748204487 * 10 ^ 70 +
        2758775750087276250985094531181380402546428936939221678600079459390762) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 155 = 59 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 16 +
      16 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_154_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_154_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_155_prefix_zero :
    (∑ x ∈ Finset.range 60,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (155 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (155 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_155_suffix_zero :
    (∑ x ∈ Finset.range 17,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (155 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_155 :
    recurrence2B4A6.coeff 155 =
      ((89027435149548123494983580776040949561121153281819073458799 * 10 ^ 70 +
        9561867225029146355386639466966437351559351389264461761598563092998539) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 156 = 60 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 15 +
      17 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_155_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_155_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_156_prefix_zero :
    (∑ x ∈ Finset.range 61,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (156 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (156 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_156_suffix_zero :
    (∑ x ∈ Finset.range 18,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (156 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_156 :
    recurrence2B4A6.coeff 156 =
      -((48823788338325376421894512612574394941750515618432368559439 * 10 ^ 70 +
        2937909117218347970728716364451456007514327078067005497351340638429057) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 157 = 61 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 14 +
      18 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_156_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_156_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_157_prefix_zero :
    (∑ x ∈ Finset.range 62,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (157 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (157 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_157_suffix_zero :
    (∑ x ∈ Finset.range 19,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (157 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_157 :
    recurrence2B4A6.coeff 157 =
      ((20879954461356406143546039659635541507456914957904206974231 * 10 ^ 70 +
        8043960693624704584616064576169437115708800039402247755590205567181689) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 158 = 62 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 13 +
      19 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_157_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_157_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_158_prefix_zero :
    (∑ x ∈ Finset.range 63,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (158 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (158 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_158_suffix_zero :
    (∑ x ∈ Finset.range 20,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (158 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_158 :
    recurrence2B4A6.coeff 158 =
      -((4255539984411748005757113954732477502436230116867693938160 * 10 ^ 70 +
        7720214685880256569271958369930518782802228695268212388517604424630339) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 159 = 63 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 12 +
      20 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_158_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_158_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_159_prefix_zero :
    (∑ x ∈ Finset.range 64,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (159 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (159 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_159_suffix_zero :
    (∑ x ∈ Finset.range 21,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (159 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_159 :
    recurrence2B4A6.coeff 159 =
      -((3740037666814230517958744670247617770574048801688729206966 * 10 ^ 70 +
        5139455310314050132715924310819125942623920121038644480652679402362935) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 160 = 64 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 11 +
      21 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_159_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_159_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_160_prefix_zero :
    (∑ x ∈ Finset.range 65,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (160 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (160 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_160_suffix_zero :
    (∑ x ∈ Finset.range 22,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (160 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_160 :
    recurrence2B4A6.coeff 160 =
      ((6207820623704780986750904206664088486765994241615759832256 * 10 ^ 70 +
        8485554799979476857275365689649908431558517927845143933146217046001999) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 161 = 65 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 10 +
      22 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_160_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_160_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_161_prefix_zero :
    (∑ x ∈ Finset.range 66,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (161 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (161 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_161_suffix_zero :
    (∑ x ∈ Finset.range 23,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (161 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_161 :
    recurrence2B4A6.coeff 161 =
      -((5786670345705142171951532029389288196038136299526568440570 * 10 ^ 70 +
        9641430502795753951424383520021060972627789016646777557835698628123764) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 162 = 66 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 9 +
      23 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_161_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_161_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_162_prefix_zero :
    (∑ x ∈ Finset.range 67,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (162 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (162 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_162_suffix_zero :
    (∑ x ∈ Finset.range 24,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (162 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_162 :
    recurrence2B4A6.coeff 162 =
      ((4292842837602658560497531543696641141657786491973485247750 * 10 ^ 70 +
        6795372306066073164895201473224223315271176443181806099308876095663990) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 163 = 67 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 8 +
      24 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_162_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_162_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_163_prefix_zero :
    (∑ x ∈ Finset.range 68,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (163 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (163 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_163_suffix_zero :
    (∑ x ∈ Finset.range 25,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (163 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_163 :
    recurrence2B4A6.coeff 163 =
      -((2738387609970292815896437723476113731749784804194003562131 * 10 ^ 70 +
        2418085759593434222294834261408066141061288249051629404473748595151855) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 164 = 68 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 7 +
      25 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_163_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_163_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_164_prefix_zero :
    (∑ x ∈ Finset.range 69,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (164 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (164 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_164_suffix_zero :
    (∑ x ∈ Finset.range 26,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (164 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_164 :
    recurrence2B4A6.coeff 164 =
      ((1540559524265072987931990961875684702070250851806561341302 * 10 ^ 70 +
        3130455838889850016771173029106326339309964033487370456096904628009880) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 165 = 69 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 6 +
      26 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_164_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_164_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_165_prefix_zero :
    (∑ x ∈ Finset.range 70,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (165 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (165 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_165_suffix_zero :
    (∑ x ∈ Finset.range 27,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (165 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_165 :
    recurrence2B4A6.coeff 165 =
      -((767720026190140699794025545558522474398809321849657134138 * 10 ^ 70 +
        8452895950914467152755695394971350888954336913392741971830015371109888) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 166 = 70 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 5 +
      27 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_165_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_165_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_166_prefix_zero :
    (∑ x ∈ Finset.range 71,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (166 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (166 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_166_suffix_zero :
    (∑ x ∈ Finset.range 28,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (166 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_166 :
    recurrence2B4A6.coeff 166 =
      ((334838603885975198110959054846390029302834260781931817150 * 10 ^ 70 +
        2874282595970941285934533786021518078542614073989872700973068318905193) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 167 = 71 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 4 +
      28 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_166_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_166_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_167_prefix_zero :
    (∑ x ∈ Finset.range 72,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (167 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (167 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_167_suffix_zero :
    (∑ x ∈ Finset.range 29,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (167 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_167 :
    recurrence2B4A6.coeff 167 =
      -((122932229463956391801055569194755858770172229158860210723 * 10 ^ 70 +
        3105189035014745196796635115464196906231634994038222217578059764493221) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 168 = 72 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 3 +
      29 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_167_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_167_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_168_prefix_zero :
    (∑ x ∈ Finset.range 73,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (168 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (168 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_168_suffix_zero :
    (∑ x ∈ Finset.range 30,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (168 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_168 :
    recurrence2B4A6.coeff 168 =
      ((33630067516803103889392081504532269600533764454382736990 * 10 ^ 70 +
        2194074522049202994175111167514568678423355669814727410460448635608347) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 169 = 73 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 2 +
      30 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_168_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_168_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_169_prefix_zero :
    (∑ x ∈ Finset.range 74,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (169 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (169 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_169_suffix_zero :
    (∑ x ∈ Finset.range 31,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (169 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_169 :
    recurrence2B4A6.coeff 169 =
      -((2902087210883775847595577315817317751170886456279706655 * 10 ^ 70 +
        2279575615857408964859862720747877678858983755757399304187152379584808) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 170 = 74 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 1 +
      31 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_169_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_169_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_170_prefix_zero :
    (∑ x ∈ Finset.range 75,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (170 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (170 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_170_suffix_zero :
    (∑ x ∈ Finset.range 32,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (170 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_170 :
    recurrence2B4A6.coeff 170 =
      -((4210884402935127287451854223987233315583143233549158517 * 10 ^ 70 +
        9946594131612401978441742432500416686201930353990488558178477513804515) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 171 = 75 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_170_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_170_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_171_prefix_zero :
    (∑ x ∈ Finset.range 76,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (171 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (171 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_171_suffix_zero :
    (∑ x ∈ Finset.range 33,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (171 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_171 :
    recurrence2B4A6.coeff 171 =
      ((3875892886302227381020103923544121325743335345285797683 * 10 ^ 70 +
        1090427784229989561458405224186259697173073801042204171533706838046818) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 172 = 76 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 31 +
      33 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_171_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_171_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_172_prefix_zero :
    (∑ x ∈ Finset.range 77,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (172 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (172 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_172_suffix_zero :
    (∑ x ∈ Finset.range 34,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (172 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_172 :
    recurrence2B4A6.coeff 172 =
      -((2246235212903088815096278494205337737222961918763712179 * 10 ^ 70 +
        8717381337095174227151065839860645492981488316651445494876646506080618) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 173 = 77 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 30 +
      34 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_172_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_172_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_173_prefix_zero :
    (∑ x ∈ Finset.range 78,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (173 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (173 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_173_suffix_zero :
    (∑ x ∈ Finset.range 35,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (173 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_173 :
    recurrence2B4A6.coeff 173 =
      ((1038477056627288769159761358646455784480585759416106689 * 10 ^ 70 +
        3678257369583196447250057744344381358287921598461185204403227934665818) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 174 = 78 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 29 +
      35 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_173_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_173_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_174_prefix_zero :
    (∑ x ∈ Finset.range 79,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (174 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (174 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_174_suffix_zero :
    (∑ x ∈ Finset.range 36,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (174 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_174 :
    recurrence2B4A6.coeff 174 =
      -((404211156623766720101241094474959126169940895757600881 * 10 ^ 70 +
        5822074205260847503694405245867555851603246146874976032575635742556668) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 175 = 79 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 28 +
      36 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_174_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_174_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_175_prefix_zero :
    (∑ x ∈ Finset.range 80,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (175 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (175 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_175_suffix_zero :
    (∑ x ∈ Finset.range 37,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (175 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_175 :
    recurrence2B4A6.coeff 175 =
      ((133201596250581812292239290915284964719661330341779712 * 10 ^ 70 +
        6492831659074114102251837828460219306575925947376409143725908204193158) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 176 = 80 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 27 +
      37 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_175_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_175_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_176_prefix_zero :
    (∑ x ∈ Finset.range 81,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (176 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (176 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_176_suffix_zero :
    (∑ x ∈ Finset.range 38,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (176 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_176 :
    recurrence2B4A6.coeff 176 =
      -((36003545529197795331768076335998456305349002080129846 * 10 ^ 70 +
        8995011678050907579779225609604124835337735606900040503885411078051227) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 177 = 81 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 26 +
      38 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_176_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_176_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_177_prefix_zero :
    (∑ x ∈ Finset.range 82,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (177 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (177 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_177_suffix_zero :
    (∑ x ∈ Finset.range 39,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (177 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_177 :
    recurrence2B4A6.coeff 177 =
      ((7084272224417020540693394849512262889899178474801788 * 10 ^ 70 +
        2061788882154680207782929237508432318329741076504472953464810359728923) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 178 = 82 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 25 +
      39 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_177_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_177_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_178_prefix_zero :
    (∑ x ∈ Finset.range 83,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (178 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (178 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_178_suffix_zero :
    (∑ x ∈ Finset.range 40,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (178 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_178 :
    recurrence2B4A6.coeff 178 =
      -((427299017218612613218493918899670573303062773701236 * 10 ^ 70 +
        3711360924451444889191929423064281716843746067906163450195795660022047) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 179 = 83 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 24 +
      40 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_178_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_178_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_179_prefix_zero :
    (∑ x ∈ Finset.range 84,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (179 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (179 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_179_suffix_zero :
    (∑ x ∈ Finset.range 41,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (179 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_179 :
    recurrence2B4A6.coeff 179 =
      -((431174287544332595187564746825933712475903012064248 * 10 ^ 70 +
        6593200402107591335972791058344337450157946305892755434463977225206056) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 180 = 84 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 23 +
      41 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_179_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_179_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_180_prefix_zero :
    (∑ x ∈ Finset.range 85,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (180 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (180 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_180_suffix_zero :
    (∑ x ∈ Finset.range 42,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (180 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_180 :
    recurrence2B4A6.coeff 180 =
      ((265401557599305710444160011180470018310722529008862 * 10 ^ 70 +
        5577011377208768847084029751807324333700099501550105109254953606123403) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 181 = 85 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 22 +
      42 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_180_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_180_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_181_prefix_zero :
    (∑ x ∈ Finset.range 86,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (181 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (181 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_181_suffix_zero :
    (∑ x ∈ Finset.range 43,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (181 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_181 :
    recurrence2B4A6.coeff 181 =
      -((99706198399161697508604003201607493314225234835339 * 10 ^ 70 +
        0665080378033798440823084276461382277487488158598304191303261712095825) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 182 = 86 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 21 +
      43 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_181_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_181_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_182_prefix_zero :
    (∑ x ∈ Finset.range 87,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (182 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (182 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_182_suffix_zero :
    (∑ x ∈ Finset.range 44,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (182 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_182 :
    recurrence2B4A6.coeff 182 =
      ((28622444203060660198459258037090480543210719923275 * 10 ^ 70 +
        8816121597595905114205873734832894313497914444956808554425279964235786) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 183 = 87 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 20 +
      44 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_182_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_182_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_183_prefix_zero :
    (∑ x ∈ Finset.range 88,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (183 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (183 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_183_suffix_zero :
    (∑ x ∈ Finset.range 45,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (183 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_183 :
    recurrence2B4A6.coeff 183 =
      -((6467113770502028500965715480413948883929052425269 * 10 ^ 70 +
        3802436474377654362467727362533948933928554742058089489293619463361077) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 184 = 88 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 19 +
      45 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_183_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_183_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_184_prefix_zero :
    (∑ x ∈ Finset.range 89,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (184 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (184 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_184_suffix_zero :
    (∑ x ∈ Finset.range 46,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (184 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_184 :
    recurrence2B4A6.coeff 184 =
      ((1080691813158337491748641964225757395765489450335 * 10 ^ 70 +
        5032762419579884089553293824776937509086940301889174533771988599262022) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 185 = 89 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 18 +
      46 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_184_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_184_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_185_prefix_zero :
    (∑ x ∈ Finset.range 90,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (185 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (185 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_185_suffix_zero :
    (∑ x ∈ Finset.range 47,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (185 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_185 :
    recurrence2B4A6.coeff 185 =
      -((92003625266852612624244317825457898162277066552 * 10 ^ 70 +
        7196355568046833361390646996795600629123231320527654989567964750795590) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 186 = 90 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 17 +
      47 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_185_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_185_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_186_prefix_zero :
    (∑ x ∈ Finset.range 91,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (186 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (186 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_186_suffix_zero :
    (∑ x ∈ Finset.range 48,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (186 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_186 :
    recurrence2B4A6.coeff 186 =
      -((16931611041064095463860079931195314392373191824 * 10 ^ 70 +
        7763301130278843406071424780410407006586430031027572297982598507776588) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 187 = 91 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 16 +
      48 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_186_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_186_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_187_prefix_zero :
    (∑ x ∈ Finset.range 92,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (187 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (187 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_187_suffix_zero :
    (∑ x ∈ Finset.range 49,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (187 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_187 :
    recurrence2B4A6.coeff 187 =
      ((10053275997593281270235204114145997176783664905 * 10 ^ 70 +
        3578933857242825490347483219855599780156277204494560287384379388926004) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 188 = 92 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 15 +
      49 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_187_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_187_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_188_prefix_zero :
    (∑ x ∈ Finset.range 93,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (188 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (188 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_188_suffix_zero :
    (∑ x ∈ Finset.range 50,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (188 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_188 :
    recurrence2B4A6.coeff 188 =
      -((2726453162919423712006796300182256992266538169 * 10 ^ 70 +
        1064388172119798416320065933298201540844022997493157202055806350468217) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 189 = 93 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 14 +
      50 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_188_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_188_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_189_prefix_zero :
    (∑ x ∈ Finset.range 94,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (189 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (189 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_189_suffix_zero :
    (∑ x ∈ Finset.range 51,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (189 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_189 :
    recurrence2B4A6.coeff 189 =
      ((510450992336669931287061822011032650820603142 * 10 ^ 70 +
        8476264938161940676407103548523803465344247843493176812295739782119284) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 190 = 94 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 13 +
      51 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_189_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_189_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_190_prefix_zero :
    (∑ x ∈ Finset.range 95,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (190 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (190 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_190_suffix_zero :
    (∑ x ∈ Finset.range 52,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (190 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_190 :
    recurrence2B4A6.coeff 190 =
      -((65976039530229589612123890978323434233640897 * 10 ^ 70 +
        3009722628749590005208916937799647296399319255530539131847892397730721) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 191 = 95 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 12 +
      52 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_190_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_190_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_191_prefix_zero :
    (∑ x ∈ Finset.range 96,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (191 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (191 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_191_suffix_zero :
    (∑ x ∈ Finset.range 53,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (191 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_191 :
    recurrence2B4A6.coeff 191 =
      ((4084835895762713647185028542674425434405462 * 10 ^ 70 +
        0478425017852626823925008909052347390866033050797196997661751442114074) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 192 = 96 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 11 +
      53 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_191_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_191_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_192_prefix_zero :
    (∑ x ∈ Finset.range 97,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (192 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (192 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_192_suffix_zero :
    (∑ x ∈ Finset.range 54,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (192 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_192 :
    recurrence2B4A6.coeff 192 =
      ((558646861600331953408277701076803469929465 * 10 ^ 70 +
        2449239095064778098288097034220118475535751526742225411729067933086225) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 193 = 97 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 10 +
      54 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_192_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_192_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_193_prefix_zero :
    (∑ x ∈ Finset.range 98,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (193 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (193 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_193_suffix_zero :
    (∑ x ∈ Finset.range 55,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (193 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_193 :
    recurrence2B4A6.coeff 193 =
      -((218091098568696144382483205051620521175890 * 10 ^ 70 +
        1719113096860951056103916043790094280884123030859400891936763960549402) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 194 = 98 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 9 +
      55 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_193_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_193_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_194_prefix_zero :
    (∑ x ∈ Finset.range 99,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (194 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (194 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_194_suffix_zero :
    (∑ x ∈ Finset.range 56,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (194 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_194 :
    recurrence2B4A6.coeff 194 =
      ((36732469329750563972554297050343706813643 * 10 ^ 70 +
        5495573089974223180615989300451725108174203344620365719535219647370044) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 195 = 99 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 8 +
      56 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_194_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_194_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_195_prefix_zero :
    (∑ x ∈ Finset.range 100,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (195 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (195 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_195_suffix_zero :
    (∑ x ∈ Finset.range 57,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (195 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_195 :
    recurrence2B4A6.coeff 195 =
      -((3738256938564991059777260265262822572210 * 10 ^ 70 +
        1168667304031869151339843170059769608630399980279719379488169356152508) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 196 = 100 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 7 +
      57 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_195_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_195_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_196_prefix_zero :
    (∑ x ∈ Finset.range 101,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (196 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (196 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_196_suffix_zero :
    (∑ x ∈ Finset.range 58,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (196 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_196 :
    recurrence2B4A6.coeff 196 =
      ((159337179189674278587181002205452310197 * 10 ^ 70 +
        9178228012918053200278220256832018176399577604008407718635691046535024) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 197 = 101 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 6 +
      58 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_196_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_196_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_197_prefix_zero :
    (∑ x ∈ Finset.range 102,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (197 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (197 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_197_suffix_zero :
    (∑ x ∈ Finset.range 59,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (197 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_197 :
    recurrence2B4A6.coeff 197 =
      ((19040588325392159163955419118885456019 * 10 ^ 70 +
        1159634983248316085863521664853438509341771609086249919114504557984063) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 198 = 102 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 5 +
      59 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_197_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_197_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_198_prefix_zero :
    (∑ x ∈ Finset.range 103,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (198 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (198 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_198_suffix_zero :
    (∑ x ∈ Finset.range 60,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (198 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_198 :
    recurrence2B4A6.coeff 198 =
      -((4442324225233604435103908309888329470 * 10 ^ 70 +
        1697302017729714813579860061382153066295961971759035411664446368182710) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 199 = 103 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 4 +
      60 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_198_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_198_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_199_prefix_zero :
    (∑ x ∈ Finset.range 104,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (199 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (199 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_199_suffix_zero :
    (∑ x ∈ Finset.range 61,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (199 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_199 :
    recurrence2B4A6.coeff 199 =
      ((417568244400505373169370164418529914 * 10 ^ 70 +
        7839396074240981421989199282850188810795832779405028869869109996828712) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 200 = 104 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 3 +
      61 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_199_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_199_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_200_prefix_zero :
    (∑ x ∈ Finset.range 105,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (200 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (200 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_200_suffix_zero :
    (∑ x ∈ Finset.range 62,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (200 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_200 :
    recurrence2B4A6.coeff 200 =
      -((16045873083399463708608136035034207 * 10 ^ 70 +
        3317096197762901147376656379591737425930699086067703824631987677186523) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 201 = 105 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 2 +
      62 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_200_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_200_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_201_prefix_zero :
    (∑ x ∈ Finset.range 106,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (201 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (201 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_201_suffix_zero :
    (∑ x ∈ Finset.range 63,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (201 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_201 :
    recurrence2B4A6.coeff 201 =
      -((899768636556865638765587998017211 * 10 ^ 70 +
        9535114661842661135351594776781974576008059839176063547647778528108526) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 202 = 106 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 1 +
      63 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_201_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_201_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_202_prefix_zero :
    (∑ x ∈ Finset.range 107,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (202 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (202 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_202_suffix_zero :
    (∑ x ∈ Finset.range 64,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (202 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_202 :
    recurrence2B4A6.coeff 202 =
      ((158381719240183922906243739189536 * 10 ^ 70 +
        2278382021834237034239619052340729806675766666006421880465887323227595) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 203 = 107 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_202_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_202_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_203_prefix_zero :
    (∑ x ∈ Finset.range 108,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (203 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (203 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_203_suffix_zero :
    (∑ x ∈ Finset.range 65,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (203 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_203 :
    recurrence2B4A6.coeff 203 =
      -((8170128133431341637746849975263 * 10 ^ 70 +
        4938628921543539754475807564401070501557153661252186778968318302707184) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 204 = 108 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 31 +
      65 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_203_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_203_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_204_prefix_zero :
    (∑ x ∈ Finset.range 109,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (204 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (204 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_204_suffix_zero :
    (∑ x ∈ Finset.range 66,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (204 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_204 :
    recurrence2B4A6.coeff 204 =
      ((2013320173130418668493844286 * 10 ^ 70 +
        7798303097879185250523855652640585851674279729526310744413353020990841) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 205 = 109 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 30 +
      66 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_204_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_204_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_205_prefix_zero :
    (∑ x ∈ Finset.range 110,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (205 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (205 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_205_suffix_zero :
    (∑ x ∈ Finset.range 67,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (205 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_205 :
    recurrence2B4A6.coeff 205 =
      ((20088012667847254219191451930 * 10 ^ 70 +
        2043953472740931714209846075482873199643269380138042105257394773216778) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 206 = 110 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 29 +
      67 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_205_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_205_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_206_prefix_zero :
    (∑ x ∈ Finset.range 111,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (206 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (206 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_206_suffix_zero :
    (∑ x ∈ Finset.range 68,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (206 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_206 :
    recurrence2B4A6.coeff 206 =
      -((796190698150313273273635799 * 10 ^ 70 +
        4820510990585963445550610786069904573534183971738730016643961691637554) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 207 = 111 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 28 +
      68 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_206_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_206_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_207_prefix_zero :
    (∑ x ∈ Finset.range 112,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (207 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (207 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_207_suffix_zero :
    (∑ x ∈ Finset.range 69,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (207 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_207 :
    recurrence2B4A6.coeff 207 =
      -((4132909773687588518644312 * 10 ^ 70 +
        2817641671968739826390053631909030025193599756542174909494735784584930) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 208 = 112 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 27 +
      69 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_207_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_207_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_208_prefix_zero :
    (∑ x ∈ Finset.range 113,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (208 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (208 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_208_suffix_zero :
    (∑ x ∈ Finset.range 70,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (208 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_208 :
    recurrence2B4A6.coeff 208 =
      ((878416612234912446638150 * 10 ^ 70 +
        4776340106438848442131954198970449943752001377825666074254161099716612) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 209 = 113 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 26 +
      70 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_208_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_208_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_209_prefix_zero :
    (∑ x ∈ Finset.range 114,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (209 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (209 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_209_suffix_zero :
    (∑ x ∈ Finset.range 71,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (209 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_209 :
    recurrence2B4A6.coeff 209 =
      -((9763908348540467902400 * 10 ^ 70 +
        7446531902193598015226326565440832640984369578709640236390979002072111) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 210 = 114 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 25 +
      71 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_209_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_209_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_210_prefix_zero :
    (∑ x ∈ Finset.range 115,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (210 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (210 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_210_suffix_zero :
    (∑ x ∈ Finset.range 72,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (210 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_210 :
    recurrence2B4A6.coeff 210 =
      -((315359622212257371827 * 10 ^ 70 +
        0534281624616388531181042320613158891357330190081304186458142137573332) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 211 = 115 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 24 +
      72 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_210_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_210_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_211_prefix_zero :
    (∑ x ∈ Finset.range 116,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (211 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (211 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_211_suffix_zero :
    (∑ x ∈ Finset.range 73,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (211 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_211 :
    recurrence2B4A6.coeff 211 =
      ((4326486560217567664 * 10 ^ 70 +
        9290289517376472940693759204032581547284930969500471265712485856777409) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 212 = 116 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 23 +
      73 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_211_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_211_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_212_prefix_zero :
    (∑ x ∈ Finset.range 117,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (212 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (212 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_212_suffix_zero :
    (∑ x ∈ Finset.range 74,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (212 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_212 :
    recurrence2B4A6.coeff 212 =
      ((50742717958089572 * 10 ^ 70 +
        0404429493081662716054724510769658766485975100382280267575249237003137) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 213 = 117 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 22 +
      74 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_212_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_212_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_213_prefix_zero :
    (∑ x ∈ Finset.range 118,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (213 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (213 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_213_suffix_zero :
    (∑ x ∈ Finset.range 75,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (213 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_213 :
    recurrence2B4A6.coeff 213 =
      -((498666921118902 * 10 ^ 70 +
        7253399929312113001314706264967528933973453651794059787427420336869479) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 214 = 118 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 21 +
      75 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_213_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_213_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_214_prefix_zero :
    (∑ x ∈ Finset.range 119,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (214 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (214 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_214_suffix_zero :
    (∑ x ∈ Finset.range 76,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (214 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_214 :
    recurrence2B4A6.coeff 214 =
      -((4118809097180 * 10 ^ 70 +
        9437183865555306705897987046519738124376938413259654703310955303846152) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 215 = 119 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 20 +
      76 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_214_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_214_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_215_prefix_zero :
    (∑ x ∈ Finset.range 120,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (215 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (215 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_215_suffix_zero :
    (∑ x ∈ Finset.range 77,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (215 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_215 :
    recurrence2B4A6.coeff 215 =
      ((17783411926 * 10 ^ 70 +
        2815556000611328189798109759885664944454724997048384528327048554042180) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 216 = 120 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 19 +
      77 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_215_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_215_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_216_prefix_zero :
    (∑ x ∈ Finset.range 121,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (216 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (216 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_216_suffix_zero :
    (∑ x ∈ Finset.range 78,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (216 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_216 :
    recurrence2B4A6.coeff 216 =
      ((138667632 * 10 ^ 70 +
        3550345628038888053737410836687532761290250365168091783509037634922402) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 217 = 121 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 18 +
      78 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_216_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_216_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_217_prefix_zero :
    (∑ x ∈ Finset.range 122,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (217 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (217 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_217_suffix_zero :
    (∑ x ∈ Finset.range 79,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (217 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_217 :
    recurrence2B4A6.coeff 217 =
      -((227824 * 10 ^ 70 +
        1406987048251226705454829928429286213976626352852178542989321643719482) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 218 = 122 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 17 +
      79 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_217_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_217_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_218_prefix_zero :
    (∑ x ∈ Finset.range 123,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (218 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (218 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_218_suffix_zero :
    (∑ x ∈ Finset.range 80,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (218 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_218 :
    recurrence2B4A6.coeff 218 =
      -((1812 * 10 ^ 70 +
        8781872071220237726585419056007659446267220642018337415303002352145799) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 219 = 123 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 16 +
      80 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_218_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_218_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_219_prefix_zero :
    (∑ x ∈ Finset.range 124,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (219 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (219 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_219_suffix_zero :
    (∑ x ∈ Finset.range 81,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (219 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_219 :
    recurrence2B4A6.coeff 219 =
      ((1 * 10 ^ 70 +
        7970301362802963577579432435703810551799215401776589836049980782449907) : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 220 = 124 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 15 +
      81 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_219_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_219_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_220_prefix_zero :
    (∑ x ∈ Finset.range 125,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (220 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (220 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_220_suffix_zero :
    (∑ x ∈ Finset.range 82,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (220 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_220 :
    recurrence2B4A6.coeff 220 =
      (99991111620497825997282022565416250318154286653733808264363934627809 : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 221 = 125 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 14 +
      82 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_220_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_220_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_221_prefix_zero :
    (∑ x ∈ Finset.range 126,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (221 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (221 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_221_suffix_zero :
    (∑ x ∈ Finset.range 83,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (221 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_221 :
    recurrence2B4A6.coeff 221 =
      (-103549026305853853491964020802027163510391556225093978322807143735 : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 222 = 126 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 13 +
      83 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_221_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_221_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_222_prefix_zero :
    (∑ x ∈ Finset.range 127,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (222 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (222 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_222_suffix_zero :
    (∑ x ∈ Finset.range 84,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (222 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_222 :
    recurrence2B4A6.coeff 222 =
      (-182735127921126109049827826220209876853659389351823153114958373 : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 223 = 127 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 12 +
      84 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_222_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_222_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B4A6_coeff_223_prefix_zero :
    (∑ x ∈ Finset.range 128,
      remainder3Coefficient4.coeff x * remainder2Coefficient6.coeff (223 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (223 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B4A6_coeff_223_suffix_zero :
    (∑ x ∈ Finset.range 85,
      remainder3Coefficient4.coeff (139 + x) *
        remainder2Coefficient6.coeff (223 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2B4A6_coeff_223 :
    recurrence2B4A6.coeff 223 =
      (221004684282954498531389502610718726903526347183169015695618 : ℚ) := by
  unfold recurrence2B4A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 224 = 128 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 11 +
      85 by norm_num, Finset.sum_range_add]
  rw [recurrence2B4A6_coeff_223_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B4A6_coeff_223_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
