/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB5
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupA6
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: B5A6 coefficient convolution

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/

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

theorem recurrence2B5A6_coeff_0 :
    recurrence2B5A6.coeff 0 =
      (-38784 : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_1 :
    recurrence2B5A6.coeff 1 =
      (-9554040 : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_2 :
    recurrence2B5A6.coeff 2 =
      (-775611249548 : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_3 :
    recurrence2B5A6.coeff 3 =
      (-54761791975288 : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_4 :
    recurrence2B5A6.coeff 4 =
      (671998376665411956 : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_5 :
    recurrence2B5A6.coeff 5 =
      (-458891331588737950804 : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_6 :
    recurrence2B5A6.coeff 6 =
      (417202843530225184084702 : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_7 :
    recurrence2B5A6.coeff 7 =
      (-131042986046673025848100306 : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_8 :
    recurrence2B5A6.coeff 8 =
      (25738914503343946042763378280 : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_9 :
    recurrence2B5A6.coeff 9 =
      (-3045413394047472082237257527604 : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_10 :
    recurrence2B5A6.coeff 10 =
      (145189759210565985029649602088632 : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_11 :
    recurrence2B5A6.coeff 11 =
      (7218716176449186645996165109537727 : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_12 :
    recurrence2B5A6.coeff 12 =
      (-1756345587377771328491190821512483117 : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_13 :
    recurrence2B5A6.coeff 13 =
      (130920166036798931638893652742492404182 : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_14 :
    recurrence2B5A6.coeff 14 =
      (-5027754702255942062074150609405946227916 : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_15 :
    recurrence2B5A6.coeff 15 =
      (99723248684694938604571484125414054689149 : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_16 :
    recurrence2B5A6.coeff 16 =
      (-560061588122533137554984691161946116577834 : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_17 :
    recurrence2B5A6.coeff 17 =
      (-51925565642336704706998342281132929545779273 : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_18 :
    recurrence2B5A6.coeff 18 =
      (8451507781218615056302501601500508615923156461 : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_19 :
    recurrence2B5A6.coeff 19 =
      (-648575333057055657489243912496203991309704442923 : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_20 :
    recurrence2B5A6.coeff 20 =
      (25311353116055407625806245894485680828353791437793 : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_21 :
    recurrence2B5A6.coeff 21 =
      (-434027262744381611712679130012364137908407996399406 : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_22 :
    recurrence2B5A6.coeff 22 =
      (-3388169497864445860243440423704843608128708269730719 : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_23 :
    recurrence2B5A6.coeff 23 =
      (272702117880662339452946502977807531961850085423063582 : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_24 :
    recurrence2B5A6.coeff 24 =
      (-819729594946693267742823923408919503051814574129234282 : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_25 :
    recurrence2B5A6.coeff 25 =
      (-248625948881223657758933251248713935803906589499229518506 : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_26 :
    recurrence2B5A6.coeff 26 =
      (9724860811484387472764468222604510827894093501392185137283 : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_27 :
    recurrence2B5A6.coeff 27 =
      (-215609852928463842160613069741620260846771591438452698527155 : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_28 :
    recurrence2B5A6.coeff 28 =
      (3653963011629553778851149439276719487415789785902075694119236 : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_29 :
    recurrence2B5A6.coeff 29 =
      (-59702259728743277704955111731351365971952471375705556144610903 : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_30 :
    recurrence2B5A6.coeff 30 =
      (1046228122117749584202212827173027149074034142978822137348909974 : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_31 :
    recurrence2B5A6.coeff 31 =
      (-17131946436112956899557809589131891169297049014501192697168788008 : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_32 :
    recurrence2B5A6.coeff 32 =
      (212532766525866856145952914687292164538516884666381446667056896506 : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_33 :
    recurrence2B5A6.coeff 33 =
      (-1353939162632490856699811968178905835009737991024114247356822505565 : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_34 :
    recurrence2B5A6.coeff 34 =
      (-14125872334864864303032942414187426289960784928828482724740170689598 : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_35 :
    recurrence2B5A6.coeff 35 =
      (629229390164346779378803412430118698889182362460713937905204020403351 : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_36 :
    recurrence2B5A6.coeff 36 =
      -((1 * 10 ^ 70 +
        2850173709505610543627702315559423313709243275661149556312169719514750) : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_37 :
    recurrence2B5A6.coeff 37 =
      ((20 * 10 ^ 70 +
        7144335680817545303347206925567033152439652496238499625679140126907460) : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_38 :
    recurrence2B5A6.coeff 38 =
      -((295 * 10 ^ 70 +
        8288074964774824746952739382698447301666523384471557514784259912420176) : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_39 :
    recurrence2B5A6.coeff 39 =
      ((3839 * 10 ^ 70 +
        2554974081308882542900288428299820358471051423206469163285336379695072) : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_40 :
    recurrence2B5A6.coeff 40 =
      -((45026 * 10 ^ 70 +
        2089210945820659467711790570437550030651442848334127054322443519717847) : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_41 :
    recurrence2B5A6.coeff 41 =
      ((475416 * 10 ^ 70 +
        7323072393559174385681791739414177623611770439900184582919361402329105) : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_42 :
    recurrence2B5A6.coeff 42 =
      -((4566774 * 10 ^ 70 +
        0413120235166560983961208905169658390966752472052683608883411744372292) : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_43 :
    recurrence2B5A6.coeff 43 =
      ((40717626 * 10 ^ 70 +
        5355333304940436578101036270523659214125637840181524347629768707731624) : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_44 :
    recurrence2B5A6.coeff 44 =
      -((342240809 * 10 ^ 70 +
        3125862709346907423237947105377724365320289536508139406396320854826497) : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_45 :
    recurrence2B5A6.coeff 45 =
      ((2711826811 * 10 ^ 70 +
        2870107661934895200144809478894502006756333313089619236019424514761084) : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_46 :
    recurrence2B5A6.coeff 46 =
      -((20034710974 * 10 ^ 70 +
        3386895313670888366429435510300761648923514450592293188341028360526093) : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_47 :
    recurrence2B5A6.coeff 47 =
      ((137025090621 * 10 ^ 70 +
        5645029030403454986574972597427985761081720956979211563845300337553252) : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_48 :
    recurrence2B5A6.coeff 48 =
      -((873422641013 * 10 ^ 70 +
        0828898073725481162371034463815140453621105272138822023322184654816913) : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_49 :
    recurrence2B5A6.coeff 49 =
      ((5275992517425 * 10 ^ 70 +
        8665661690777834586349378464234913420370743588942476303983572520564504) : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_50 :
    recurrence2B5A6.coeff 50 =
      -((30544397764441 * 10 ^ 70 +
        3130403644057616742408264033894172044015822976064170954027006388586610) : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_51 :
    recurrence2B5A6.coeff 51 =
      ((168353756978784 * 10 ^ 70 +
        0524256981372877473655543970123135377344694452455367355636372517863413) : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_52 :
    recurrence2B5A6.coeff 52 =
      -((865887436529464 * 10 ^ 70 +
        9766108984917799149587362322276037277768678672733851758377954083379574) : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_53 :
    recurrence2B5A6.coeff 53 =
      ((4082120175438124 * 10 ^ 70 +
        1870670741861117309845704478314019775365909018251174782499930164418570) : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_54 :
    recurrence2B5A6.coeff 54 =
      -((17642206531469258 * 10 ^ 70 +
        4629691714924157628307340776348932247574832662180690933152714835457195) : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_55 :
    recurrence2B5A6.coeff 55 =
      ((72476375771213164 * 10 ^ 70 +
        3718279689081830629014806259795302093982170629353442469590962069554866) : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_56 :
    recurrence2B5A6.coeff 56 =
      -((305030011094367821 * 10 ^ 70 +
        3937617592548831669563790292613392676623906227601613100872780934029888) : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_57 :
    recurrence2B5A6.coeff 57 =
      ((1349156681612964641 * 10 ^ 70 +
        3723430134239118290787511738937545407601788077646020239622169133758627) : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_58 :
    recurrence2B5A6.coeff 58 =
      -((5419865047269667381 * 10 ^ 70 +
        7293732058696238651708957554444465935340886029091044368663667317750549) : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_59 :
    recurrence2B5A6.coeff 59 =
      ((13933964984859365920 * 10 ^ 70 +
        6205306244015636153505760594051402812449208061699689063780890020183301) : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_60 :
    recurrence2B5A6.coeff 60 =
      ((4723161816607433501 * 10 ^ 70 +
        6875476980494928731393022104087098835202777601133565956129425288494384) : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_61 :
    recurrence2B5A6.coeff 61 =
      -((145054629643307055065 * 10 ^ 70 +
        3049888152975820155330356321144832196037635931104000287731274256010886) : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_62 :
    recurrence2B5A6.coeff 62 =
      -((365600844222568606955 * 10 ^ 70 +
        5948243904459683720412606288797675926575496892229568571948444490108782) : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_63 :
    recurrence2B5A6.coeff 63 =
      ((7827135948682625200184 * 10 ^ 70 +
        3948139478133752792930090126353898193801339915636638170166907659455286) : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_64 :
    recurrence2B5A6.coeff 64 =
      -((26831072876743093606702 * 10 ^ 70 +
        9548193278148188602643939503975140094297999080911224192414087705835919) : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_65 :
    recurrence2B5A6.coeff 65 =
      -((82698614986138283938673 * 10 ^ 70 +
        7714806264530922146651437832753744964973487329816455025574987367305319) : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_66 :
    recurrence2B5A6.coeff 66 =
      ((940949275305094182600761 * 10 ^ 70 +
        1504275469979386410615276370047256798664246941974485101455456485630542) : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_67 :
    recurrence2B5A6.coeff 67 =
      -((1854253565410330450044076 * 10 ^ 70 +
        7083413291459761231022563937787208449978442936112306079401536607492307) : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_68 :
    recurrence2B5A6.coeff 68 =
      -((10020053534756363371535479 * 10 ^ 70 +
        0820189444446390244056167809269356179059635127167349626005462951641167) : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_69 :
    recurrence2B5A6.coeff 69 =
      ((55234172680815827978678854 * 10 ^ 70 +
        6192548225367249199996515603711587460062796159883195231140244576033379) : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_70 :
    recurrence2B5A6.coeff 70 =
      ((648822825431784687383058 * 10 ^ 70 +
        7284747970515532151780269701491950703507084562064054730941924459530458) : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_71 :
    recurrence2B5A6.coeff 71 =
      -((497853787055094108373774414 * 10 ^ 70 +
        7752499345475618732191373115912396227191097860299638434383547314314866) : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_72 :
    recurrence2B5A6.coeff 72 =
      -((629478091693482204770533067 * 10 ^ 70 +
        3369780158639009110456351139085642876173870549453156460547007041770530) : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_73 :
    recurrence2B5A6.coeff 73 =
      ((6503574031479910330778688207 * 10 ^ 70 +
        1138082535351790390646306581726112085152434578952050861665381992002732) : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_74 :
    recurrence2B5A6.coeff 74 =
      ((62509599535327564196284526432 * 10 ^ 70 +
        3989365432037486646569497699763957210734759419553786279807528033262938) : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_75 :
    recurrence2B5A6.coeff 75 =
      -((516258249782494034504715459292 * 10 ^ 70 +
        4367585762201113955561356284154302039125782913749043300524129498266031) : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_76 :
    recurrence2B5A6.coeff 76 =
      ((35877995915347627709310867923 * 10 ^ 70 +
        6971194446395216373384250003801485457292948936311961829649039258694708) : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_77 :
    recurrence2B5A6.coeff 77 =
      ((13872279905335386121479694888642 * 10 ^ 70 +
        7403789588892062931883427578705873108596361969084337660310691575427165) : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_78 :
    recurrence2B5A6.coeff 78 =
      -((54898150027486896362061656598572 * 10 ^ 70 +
        8718711831868152289484060344192558311246676011023548127428084965646692) : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_79 :
    recurrence2B5A6.coeff 79 =
      -((87485120439113821565966518425420 * 10 ^ 70 +
        9216853886651646182677079525661992638831874323824503537083330928105425) : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_80 :
    recurrence2B5A6.coeff 80 =
      ((1375368990497570517927063704147916 * 10 ^ 70 +
        0146594605576930079929138251749776405722629778002289656969207806277424) : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_81 :
    recurrence2B5A6.coeff 81 =
      -((3199350001008490085151948905864516 * 10 ^ 70 +
        3637723152351264540765778956459204190313949655335168129446543737794692) : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_82 :
    recurrence2B5A6.coeff 82 =
      -((12323958033081917857652704457884656 * 10 ^ 70 +
        9136969446475168635923531374474680312590409716679409673145044799891705) : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_83 :
    recurrence2B5A6.coeff 83 =
      ((89604393549559528617316178273785840 * 10 ^ 70 +
        9907736239380774895542197681404605321616887052009456180441415382250826) : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_84 :
    recurrence2B5A6.coeff 84 =
      -((88465184035476883841793600843188809 * 10 ^ 70 +
        0909148845743279853831617977431402250663916645139679220645524063245793) : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_85 :
    recurrence2B5A6.coeff 85 =
      -((1039595670346308433351247073231710293 * 10 ^ 70 +
        9483492132519939528916681124360782279232133081685642046086809640862555) : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_86 :
    recurrence2B5A6.coeff 86 =
      ((4231191002979017439312580626380009867 * 10 ^ 70 +
        7251561268671653880887335027315785601178039816973249883563470884506213) : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_87 :
    recurrence2B5A6.coeff 87 =
      ((2596507612314067353629904197373429252 * 10 ^ 70 +
        1421536852546729392879604693356191853947166560642304304314602641426276) : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_88 :
    recurrence2B5A6.coeff 88 =
      -((66104339473407325387996381106785174005 * 10 ^ 70 +
        6582560301685635697506702914872175351359557957904090198112058952893874) : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_89 :
    recurrence2B5A6.coeff 89 =
      ((153845563944043247019666783854624082686 * 10 ^ 70 +
        4266035342931324643287020899603119395264010718211083621192354778869209) : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_90 :
    recurrence2B5A6.coeff 90 =
      ((451642209882154032714194057379926673847 * 10 ^ 70 +
        3069284448505985141120073597225689390051687348755410658016947037969126) : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_91 :
    recurrence2B5A6.coeff 91 =
      -((3432359112521979311837186332256155160110 * 10 ^ 70 +
        9002586353146347952903703099612612675645578422066230126154709765113894) : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_92 :
    recurrence2B5A6.coeff 92 =
      ((4668109126527003541182616102254309511252 * 10 ^ 70 +
        3831652521547210768845082428941014441022017299611150784478232850038158) : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_93 :
    recurrence2B5A6.coeff 93 =
      ((29111350330009184984308073430942352477373 * 10 ^ 70 +
        9023288168353416764441671198171308664297824818555511865679640627185379) : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_94 :
    recurrence2B5A6.coeff 94 =
      -((150181865322947720191958478623564716159471 * 10 ^ 70 +
        4343371073527686027847854683562181772683501072554284161568126370287523) : ℚ) := by
  unfold recurrence2B5A6
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

theorem recurrence2B5A6_coeff_95 :
    recurrence2B5A6.coeff 95 =
      ((133658377046658261138674563434078549981130 * 10 ^ 70 +
        5688077376467456010005848503945535893849535169316611187508063501553402) : ℚ) := by
  unfold recurrence2B5A6
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

private theorem recurrence2B5A6_coeff_96_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (96 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A6_coeff_96 :
    recurrence2B5A6.coeff 96 =
      ((1300826843714002832992835626883081839829002 * 10 ^ 70 +
        3901704557675136108158206374466926253232998758101677586284713180568335) : ℚ) := by
  unfold recurrence2B5A6
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
  rw [recurrence2B5A6_coeff_96_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_97_prefix_zero :
    (∑ x ∈ Finset.range 2,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (97 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (97 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A6_coeff_97 :
    recurrence2B5A6.coeff 97 =
      -((5674793561351797410447286912198043361012901 * 10 ^ 70 +
        7884157573995092183921129694206762394927457488427321174739177886461922) : ℚ) := by
  unfold recurrence2B5A6
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
  rw [recurrence2B5A6_coeff_97_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_98_prefix_zero :
    (∑ x ∈ Finset.range 3,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (98 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (98 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A6_coeff_98 :
    recurrence2B5A6.coeff 98 =
      ((4232665829662747373338043172000338399402871 * 10 ^ 70 +
        3976485582272896809960716166090950258272755566939912658812689237138097) : ℚ) := by
  unfold recurrence2B5A6
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
  rw [recurrence2B5A6_coeff_98_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_99_prefix_zero :
    (∑ x ∈ Finset.range 4,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (99 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (99 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A6_coeff_99 :
    recurrence2B5A6.coeff 99 =
      ((45819813261561924693296391539944189829725702 * 10 ^ 70 +
        4343489295546691394919736293053837593184986530525081334084286088741332) : ℚ) := by
  unfold recurrence2B5A6
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
  rw [recurrence2B5A6_coeff_99_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_100_prefix_zero :
    (∑ x ∈ Finset.range 5,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (100 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (100 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A6_coeff_100 :
    recurrence2B5A6.coeff 100 =
      -((191299699078982713192746499316624265292679535 * 10 ^ 70 +
        1288429330321875846060121359627449245592802121783857041232156185799724) : ℚ) := by
  unfold recurrence2B5A6
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
  rw [recurrence2B5A6_coeff_100_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_101_prefix_zero :
    (∑ x ∈ Finset.range 6,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (101 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (101 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A6_coeff_101 :
    recurrence2B5A6.coeff 101 =
      ((166798082896323668623583469010215268461065906 * 10 ^ 70 +
        4214403998932860598698637008303027643250585451183823377480114629211772) : ℚ) := by
  unfold recurrence2B5A6
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
  rw [recurrence2B5A6_coeff_101_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_102_prefix_zero :
    (∑ x ∈ Finset.range 7,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (102 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (102 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A6_coeff_102 :
    recurrence2B5A6.coeff 102 =
      ((1300604364415596138552667170543730455190727395 * 10 ^ 70 +
        9388982247017535546663838447543187610325304013510348344285407528570656) : ℚ) := by
  unfold recurrence2B5A6
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
  rw [recurrence2B5A6_coeff_102_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_103_prefix_zero :
    (∑ x ∈ Finset.range 8,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (103 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (103 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A6_coeff_103 :
    recurrence2B5A6.coeff 103 =
      -((5820120222442588690656346697925296581063522281 * 10 ^ 70 +
        3535385775131798853449962641073726025404767939332365717854047048351617) : ℚ) := by
  unfold recurrence2B5A6
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
  rw [recurrence2B5A6_coeff_103_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_104_prefix_zero :
    (∑ x ∈ Finset.range 9,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (104 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (104 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A6_coeff_104 :
    recurrence2B5A6.coeff 104 =
      ((7266514128117928314011078927730650361676573356 * 10 ^ 70 +
        9257800800662282048164838482598833966668633017703106879787723642066990) : ℚ) := by
  unfold recurrence2B5A6
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
  rw [recurrence2B5A6_coeff_104_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_105_prefix_zero :
    (∑ x ∈ Finset.range 10,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (105 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (105 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A6_coeff_105 :
    recurrence2B5A6.coeff 105 =
      ((27620558069673078631758345828882143323551402740 * 10 ^ 70 +
        6849407524026685473402669582322968731717150372414081816315842066024559) : ℚ) := by
  unfold recurrence2B5A6
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
  rw [recurrence2B5A6_coeff_105_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_106_prefix_zero :
    (∑ x ∈ Finset.range 11,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (106 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (106 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A6_coeff_106 :
    recurrence2B5A6.coeff 106 =
      -((154106631817524535152665312398807982674196300292 * 10 ^ 70 +
        8999456784410983511624098694947758297626358738207882993484726203814338) : ℚ) := by
  unfold recurrence2B5A6
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
  rw [recurrence2B5A6_coeff_106_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_107_prefix_zero :
    (∑ x ∈ Finset.range 12,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (107 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (107 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A6_coeff_107 :
    recurrence2B5A6.coeff 107 =
      ((281058920112652578895302184977082559896132171177 * 10 ^ 70 +
        3712974591177079420354233346076315838321853517871352707600821800546334) : ℚ) := by
  unfold recurrence2B5A6
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
  rw [recurrence2B5A6_coeff_107_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_108_prefix_zero :
    (∑ x ∈ Finset.range 13,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (108 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (108 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A6_coeff_108 :
    recurrence2B5A6.coeff 108 =
      ((315919973144540254248006534188786162398218626057 * 10 ^ 70 +
        9460809034724628797307823517614725592981389297212972165684980385793329) : ℚ) := by
  unfold recurrence2B5A6
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
  rw [recurrence2B5A6_coeff_108_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_109_prefix_zero :
    (∑ x ∈ Finset.range 14,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (109 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (109 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A6_coeff_109 :
    recurrence2B5A6.coeff 109 =
      -((3276522501839849682143736862337717477105233237990 * 10 ^ 70 +
        6210841020724366692382167954734110191252198603464447328411234757615131) : ℚ) := by
  unfold recurrence2B5A6
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
  rw [recurrence2B5A6_coeff_109_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_110_prefix_zero :
    (∑ x ∈ Finset.range 15,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (110 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (110 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A6_coeff_110 :
    recurrence2B5A6.coeff 110 =
      ((8565107966128855802693737810321846720251191039464 * 10 ^ 70 +
        5114248608582477912450321757624735440232746296409944551734604798873628) : ℚ) := by
  unfold recurrence2B5A6
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
  rw [recurrence2B5A6_coeff_110_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_111_prefix_zero :
    (∑ x ∈ Finset.range 16,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (111 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (111 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A6_coeff_111 :
    recurrence2B5A6.coeff 111 =
      -((4392448265973102728292502033319139424542855705619 * 10 ^ 70 +
        7443130682325796686227345440298455651424554632692103707733529926578071) : ℚ) := by
  unfold recurrence2B5A6
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
  rw [recurrence2B5A6_coeff_111_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_112_prefix_zero :
    (∑ x ∈ Finset.range 17,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (112 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (112 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A6_coeff_112 :
    recurrence2B5A6.coeff 112 =
      -((47139866491872913812875234324397532799122320528837 * 10 ^ 70 +
        9262369894500814156310924048225343372593113784808625558970232037011461) : ℚ) := by
  unfold recurrence2B5A6
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
  rw [recurrence2B5A6_coeff_112_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_113_prefix_zero :
    (∑ x ∈ Finset.range 18,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (113 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (113 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A6_coeff_113 :
    recurrence2B5A6.coeff 113 =
      ((190080875587042055842930536032338051662684048308989 * 10 ^ 70 +
        2483697202394919926631239893726917770000615813770555226533017285883117) : ℚ) := by
  unfold recurrence2B5A6
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
  rw [recurrence2B5A6_coeff_113_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_114_prefix_zero :
    (∑ x ∈ Finset.range 19,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (114 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (114 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A6_coeff_114 :
    recurrence2B5A6.coeff 114 =
      -((322295819982687675798990632983381677946557567188469 * 10 ^ 70 +
        0704023665074631118533891695008293978006892710778048170976095941336174) : ℚ) := by
  unfold recurrence2B5A6
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
  rw [recurrence2B5A6_coeff_114_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_115_prefix_zero :
    (∑ x ∈ Finset.range 20,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (115 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (115 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A6_coeff_115 :
    recurrence2B5A6.coeff 115 =
      -((163233485660436515250960397160895904933620214649650 * 10 ^ 70 +
        0953088284085711603216975310131841750565730797312762139860244633752945) : ℚ) := by
  unfold recurrence2B5A6
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
  rw [recurrence2B5A6_coeff_115_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_116_prefix_zero :
    (∑ x ∈ Finset.range 21,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (116 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (116 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A6_coeff_116 :
    recurrence2B5A6.coeff 116 =
      ((2620070916444834605964972834913641156089342332878378 * 10 ^ 70 +
        4475572188660832797718956140995141590879167888393439235780660729678504) : ℚ) := by
  unfold recurrence2B5A6
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
  rw [recurrence2B5A6_coeff_116_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_117_prefix_zero :
    (∑ x ∈ Finset.range 22,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (117 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (117 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A6_coeff_117 :
    recurrence2B5A6.coeff 117 =
      -((7897221511208887146898317543842705730849753992323790 * 10 ^ 70 +
        6092431893926259796935746390733887656074602674561194740841598285583077) : ℚ) := by
  unfold recurrence2B5A6
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
  rw [recurrence2B5A6_coeff_117_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_118_prefix_zero :
    (∑ x ∈ Finset.range 23,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (118 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (118 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A6_coeff_118 :
    recurrence2B5A6.coeff 118 =
      ((11115548229114754464987797838211564480837627437195021 * 10 ^ 70 +
        8565524307000796667477520912974231935161917439528809310107068474314649) : ℚ) := by
  unfold recurrence2B5A6
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
  rw [recurrence2B5A6_coeff_118_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_119_prefix_zero :
    (∑ x ∈ Finset.range 24,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (119 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (119 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A6_coeff_119 :
    recurrence2B5A6.coeff 119 =
      ((8168535559987283844595320080940391317022745723296985 * 10 ^ 70 +
        9460207884898234279632431543490834506017417482434439855443808279963765) : ℚ) := by
  unfold recurrence2B5A6
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
  rw [recurrence2B5A6_coeff_119_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_120_prefix_zero :
    (∑ x ∈ Finset.range 25,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (120 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (120 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A6_coeff_120 :
    recurrence2B5A6.coeff 120 =
      -((90581540945232280138396726740931046090679195520270275 * 10 ^ 70 +
        3421086595763968017379954075077409981189523390569481016810592391299485) : ℚ) := by
  unfold recurrence2B5A6
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
  rw [recurrence2B5A6_coeff_120_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_121_prefix_zero :
    (∑ x ∈ Finset.range 26,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (121 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (121 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A6_coeff_121 :
    recurrence2B5A6.coeff 121 =
      ((264257601495413075921537504213113100848731245230050563 * 10 ^ 70 +
        5723869865386810497615518873499777462642599836228062606565677629926880) : ℚ) := by
  unfold recurrence2B5A6
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
  rw [recurrence2B5A6_coeff_121_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_122_prefix_zero :
    (∑ x ∈ Finset.range 27,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (122 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (122 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A6_coeff_122 :
    recurrence2B5A6.coeff 122 =
      -((422798613900964735722545287179832723262279438798982197 * 10 ^ 70 +
        7145803513010991986413242214822925662213303710743688734362350295683879) : ℚ) := by
  unfold recurrence2B5A6
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
  rw [recurrence2B5A6_coeff_122_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_123_prefix_zero :
    (∑ x ∈ Finset.range 28,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (123 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (123 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A6_coeff_123 :
    recurrence2B5A6.coeff 123 =
      ((93475519161689878298855944290561527701628119017512611 * 10 ^ 70 +
        2156218686571295284835200273937127689231274200278998547795199493096863) : ℚ) := by
  unfold recurrence2B5A6
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
  rw [recurrence2B5A6_coeff_123_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_124_prefix_zero :
    (∑ x ∈ Finset.range 29,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (124 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (124 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A6_coeff_124 :
    recurrence2B5A6.coeff 124 =
      ((1760817251812309100560836502740167595872085838745969137 * 10 ^ 70 +
        2483660655330826767340270857131061484913515099936365114144118002026662) : ℚ) := by
  unfold recurrence2B5A6
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
  rw [recurrence2B5A6_coeff_124_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_125_prefix_zero :
    (∑ x ∈ Finset.range 30,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (125 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (125 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A6_coeff_125 :
    recurrence2B5A6.coeff 125 =
      -((6422861857635189458716449909504445779239553115793606118 * 10 ^ 70 +
        5325689073607060614895350185230384066314131237767776856192010306909073) : ℚ) := by
  unfold recurrence2B5A6
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
  rw [recurrence2B5A6_coeff_125_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_126_prefix_zero :
    (∑ x ∈ Finset.range 31,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (126 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (126 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A6_coeff_126 :
    recurrence2B5A6.coeff 126 =
      ((13729951126686308658255782353899224631812571335197864071 * 10 ^ 70 +
        8242149564341649854621454376156245395315199369317548042974479253490298) : ℚ) := by
  unfold recurrence2B5A6
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
  rw [recurrence2B5A6_coeff_126_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_127_prefix_zero :
    (∑ x ∈ Finset.range 32,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (127 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (127 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A6_coeff_127 :
    recurrence2B5A6.coeff 127 =
      -((18223651281204271788382796403127023368684892331942111194 * 10 ^ 70 +
        9298574920696712420695571387927007359648261116208583572875119767629236) : ℚ) := by
  unfold recurrence2B5A6
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
  rw [recurrence2B5A6_coeff_127_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_128_prefix_zero :
    (∑ x ∈ Finset.range 33,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (128 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (128 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A6_coeff_128 :
    recurrence2B5A6.coeff 128 =
      ((3602586341296450051538626612423969138152560414318777463 * 10 ^ 70 +
        9813493946004212650920640083477096690835713923741469132158667507034080) : ℚ) := by
  unfold recurrence2B5A6
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
  rw [recurrence2B5A6_coeff_128_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_129_prefix_zero :
    (∑ x ∈ Finset.range 34,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (129 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (129 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A6_coeff_129 :
    recurrence2B5A6.coeff 129 =
      ((61160450123225470416161657341872976648080983577828261536 * 10 ^ 70 +
        4308258764722777457154890138900446104337741732271101581362171051723146) : ℚ) := by
  unfold recurrence2B5A6
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
  rw [recurrence2B5A6_coeff_129_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_130_prefix_zero :
    (∑ x ∈ Finset.range 35,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (130 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (130 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A6_coeff_130 :
    recurrence2B5A6.coeff 130 =
      -((216881034753449729439713935575572469679360455244507024294 * 10 ^ 70 +
        8076782877733719762950906170700513465106624197950914648797171231816810) : ℚ) := by
  unfold recurrence2B5A6
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
  rw [recurrence2B5A6_coeff_130_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_131_prefix_zero :
    (∑ x ∈ Finset.range 36,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (131 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (131 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A6_coeff_131 :
    recurrence2B5A6.coeff 131 =
      ((491312593213519588987547340607055225281853965460202187170 * 10 ^ 70 +
        5947542327869007258605114126060745281534855110622856074092474604152303) : ℚ) := by
  unfold recurrence2B5A6
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
  rw [recurrence2B5A6_coeff_131_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_132_prefix_zero :
    (∑ x ∈ Finset.range 37,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (132 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (132 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A6_coeff_132 :
    recurrence2B5A6.coeff 132 =
      -((853421894441487147152814212057186617934739302454403195290 * 10 ^ 70 +
        3999206640819575180514119552720111999751102084973202689855201153428590) : ℚ) := by
  unfold recurrence2B5A6
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
  rw [recurrence2B5A6_coeff_132_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_133_prefix_zero :
    (∑ x ∈ Finset.range 38,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (133 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (133 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A6_coeff_133 :
    recurrence2B5A6.coeff 133 =
      ((1153004341719073497311889721875924040807455076652084714004 * 10 ^ 70 +
        6410125115520059423478050290643193022725192219462588055195425128807698) : ℚ) := by
  unfold recurrence2B5A6
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
  rw [recurrence2B5A6_coeff_133_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_134_prefix_zero :
    (∑ x ∈ Finset.range 39,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (134 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (134 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A6_coeff_134 :
    recurrence2B5A6.coeff 134 =
      -((1073685710136208461380453202928928373005331169603958096983 * 10 ^ 70 +
        8504046050072934760095236837987987452753252099700136553255458156672651) : ℚ) := by
  unfold recurrence2B5A6
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
  rw [recurrence2B5A6_coeff_134_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_135_prefix_zero :
    (∑ x ∈ Finset.range 40,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (135 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (135 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_135_suffix_zero :
    (∑ x ∈ Finset.range 1,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (135 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_135 :
    recurrence2B5A6.coeff 135 =
      ((143468759218230389206430650930676558615963973155366997855 * 10 ^ 70 +
        2908287664721236597501869905539684292382945383216604257068264494179798) : ℚ) := by
  unfold recurrence2B5A6
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
    rw [show 32 = 31 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_135_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_135_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_136_prefix_zero :
    (∑ x ∈ Finset.range 41,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (136 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (136 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_136_suffix_zero :
    (∑ x ∈ Finset.range 2,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (136 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_136 :
    recurrence2B5A6.coeff 136 =
      ((2156317743565859460232260469488089996969886054986203245047 * 10 ^ 70 +
        3714296586961962652149389354304518148096870376120693448399682022097324) : ℚ) := by
  unfold recurrence2B5A6
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
    rw [show 32 = 30 +
      2 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_136_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_136_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_137_prefix_zero :
    (∑ x ∈ Finset.range 42,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (137 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (137 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_137_suffix_zero :
    (∑ x ∈ Finset.range 3,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (137 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_137 :
    recurrence2B5A6.coeff 137 =
      -((6177071406110897709340797059413051357693278160836354617362 * 10 ^ 70 +
        6642984596289621510035704576904275043309163629283510868671419659265238) : ℚ) := by
  unfold recurrence2B5A6
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
    rw [show 32 = 29 +
      3 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_137_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_137_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_138_prefix_zero :
    (∑ x ∈ Finset.range 43,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (138 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (138 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_138_suffix_zero :
    (∑ x ∈ Finset.range 4,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (138 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_138 :
    recurrence2B5A6.coeff 138 =
      ((11837818665488493448838851773938903682435865589844995405835 * 10 ^ 70 +
        9405803002843559748812808612425364648681176900615726850759979553875518) : ℚ) := by
  unfold recurrence2B5A6
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
    rw [show 32 = 28 +
      4 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_138_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_138_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_139_prefix_zero :
    (∑ x ∈ Finset.range 44,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (139 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (139 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_139_suffix_zero :
    (∑ x ∈ Finset.range 5,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (139 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_139 :
    recurrence2B5A6.coeff 139 =
      -((18422537181938165192947293367212802951681544322312677423832 * 10 ^ 70 +
        1817371382853910333788291908182282325675330611541560321199212493526337) : ℚ) := by
  unfold recurrence2B5A6
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
    rw [show 32 = 27 +
      5 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_139_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_139_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_140_prefix_zero :
    (∑ x ∈ Finset.range 45,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (140 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (140 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_140_suffix_zero :
    (∑ x ∈ Finset.range 6,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (140 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_140 :
    recurrence2B5A6.coeff 140 =
      ((24572431035768422246264124040727766558683241163945594155956 * 10 ^ 70 +
        0971190094401412397581934691958357328468986977472992177175633357133019) : ℚ) := by
  unfold recurrence2B5A6
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
    rw [show 32 = 26 +
      6 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_140_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_140_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_141_prefix_zero :
    (∑ x ∈ Finset.range 46,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (141 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (141 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_141_suffix_zero :
    (∑ x ∈ Finset.range 7,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (141 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_141 :
    recurrence2B5A6.coeff 141 =
      -((28554231422681740996528568936397591015498733668005919010551 * 10 ^ 70 +
        3506878682575682974071699490922726751121487559669058703353109874895083) : ℚ) := by
  unfold recurrence2B5A6
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
    rw [show 32 = 25 +
      7 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_141_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_141_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_142_prefix_zero :
    (∑ x ∈ Finset.range 47,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (142 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (142 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_142_suffix_zero :
    (∑ x ∈ Finset.range 8,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (142 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_142 :
    recurrence2B5A6.coeff 142 =
      ((28769665994589121902594798490530601863748273725193955834350 * 10 ^ 70 +
        3537183378553252587269682861174118586243994040246664519879421143057012) : ℚ) := by
  unfold recurrence2B5A6
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
    rw [show 32 = 24 +
      8 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_142_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_142_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_143_prefix_zero :
    (∑ x ∈ Finset.range 48,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (143 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (143 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_143_suffix_zero :
    (∑ x ∈ Finset.range 9,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (143 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_143 :
    recurrence2B5A6.coeff 143 =
      -((24340346603047287987313825623517592541991427726872544422554 * 10 ^ 70 +
        5099057361230622257155461448375674981216732853071802131080482967504263) : ℚ) := by
  unfold recurrence2B5A6
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
    rw [show 32 = 23 +
      9 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_143_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_143_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_144_prefix_zero :
    (∑ x ∈ Finset.range 49,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (144 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (144 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_144_suffix_zero :
    (∑ x ∈ Finset.range 10,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (144 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_144 :
    recurrence2B5A6.coeff 144 =
      ((15528663241256443393320915404635548653932759112064803853359 * 10 ^ 70 +
        6922864337964232314203455391924513683391802465483180501545432262422413) : ℚ) := by
  unfold recurrence2B5A6
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
    rw [show 32 = 22 +
      10 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_144_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_144_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_145_prefix_zero :
    (∑ x ∈ Finset.range 50,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (145 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (145 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_145_suffix_zero :
    (∑ x ∈ Finset.range 11,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (145 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_145 :
    recurrence2B5A6.coeff 145 =
      -((3791874049045005077803638824392240419661530389959449240157 * 10 ^ 70 +
        4047389487282513091192182515829941518576785837464516431060043868548203) : ℚ) := by
  unfold recurrence2B5A6
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
    rw [show 32 = 21 +
      11 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_145_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_145_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_146_prefix_zero :
    (∑ x ∈ Finset.range 51,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (146 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (146 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_146_suffix_zero :
    (∑ x ∈ Finset.range 12,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (146 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_146 :
    recurrence2B5A6.coeff 146 =
      -((8589915153084222358899569911085422179996482610427652718872 * 10 ^ 70 +
        3333990676098169530046645075728172190892784652726078829792034839339079) : ℚ) := by
  unfold recurrence2B5A6
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
    rw [show 32 = 20 +
      12 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_146_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_146_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_147_prefix_zero :
    (∑ x ∈ Finset.range 52,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (147 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (147 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_147_suffix_zero :
    (∑ x ∈ Finset.range 13,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (147 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_147 :
    recurrence2B5A6.coeff 147 =
      ((19186203676695045180161922533754933893294537290356138022865 * 10 ^ 70 +
        4158405468866757637739934193207955709562881950998187632578000781157309) : ℚ) := by
  unfold recurrence2B5A6
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
    rw [show 32 = 19 +
      13 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_147_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_147_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_148_prefix_zero :
    (∑ x ∈ Finset.range 53,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (148 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (148 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_148_suffix_zero :
    (∑ x ∈ Finset.range 14,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (148 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_148 :
    recurrence2B5A6.coeff 148 =
      -((26130545538753442487972387761072156974866501836256819322244 * 10 ^ 70 +
        1290803143962221317360796140474151010108347934179750536062354056123084) : ℚ) := by
  unfold recurrence2B5A6
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
    rw [show 32 = 18 +
      14 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_148_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_148_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_149_prefix_zero :
    (∑ x ∈ Finset.range 54,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (149 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (149 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_149_suffix_zero :
    (∑ x ∈ Finset.range 15,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (149 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_149 :
    recurrence2B5A6.coeff 149 =
      ((28606159976423835619595431625225982641689695796304024265503 * 10 ^ 70 +
        8388177555126969513846367162560698145261580482614366880679660440901955) : ℚ) := by
  unfold recurrence2B5A6
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
    rw [show 32 = 17 +
      15 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_149_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_149_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_150_prefix_zero :
    (∑ x ∈ Finset.range 55,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (150 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (150 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_150_suffix_zero :
    (∑ x ∈ Finset.range 16,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (150 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_150 :
    recurrence2B5A6.coeff 150 =
      -((26942859582643004968477672810553056988960046858646580054849 * 10 ^ 70 +
        2510707770956105023496804251577112190718135896376055299811082060294918) : ℚ) := by
  unfold recurrence2B5A6
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
    rw [show 32 = 16 +
      16 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_150_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_150_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_151_prefix_zero :
    (∑ x ∈ Finset.range 56,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (151 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (151 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_151_suffix_zero :
    (∑ x ∈ Finset.range 17,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (151 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_151 :
    recurrence2B5A6.coeff 151 =
      ((22338022591824665694075010471763333159430437738846221144442 * 10 ^ 70 +
        2357096143804276536596348818330222069320073906667053558190960894873706) : ℚ) := by
  unfold recurrence2B5A6
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
    rw [show 32 = 15 +
      17 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_151_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_151_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_152_prefix_zero :
    (∑ x ∈ Finset.range 57,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (152 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (152 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_152_suffix_zero :
    (∑ x ∈ Finset.range 18,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (152 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_152 :
    recurrence2B5A6.coeff 152 =
      -((16360338360673668735657824186371217621510949997752307905757 * 10 ^ 70 +
        4671908352282809227327664617779524597711573246860068255107440409583352) : ℚ) := by
  unfold recurrence2B5A6
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
    rw [show 32 = 14 +
      18 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_152_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_152_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_153_prefix_zero :
    (∑ x ∈ Finset.range 58,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (153 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (153 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_153_suffix_zero :
    (∑ x ∈ Finset.range 19,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (153 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_153 :
    recurrence2B5A6.coeff 153 =
      ((10450434108008480708891714671552092775044306296809865082600 * 10 ^ 70 +
        9699234406953846875111312849573924561718920294657429568653473840614375) : ℚ) := by
  unfold recurrence2B5A6
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
    rw [show 32 = 13 +
      19 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_153_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_153_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_154_prefix_zero :
    (∑ x ∈ Finset.range 59,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (154 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (154 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_154_suffix_zero :
    (∑ x ∈ Finset.range 20,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (154 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_154 :
    recurrence2B5A6.coeff 154 =
      -((5587906624862406401353012253271504211787737844374676170304 * 10 ^ 70 +
        5726976230142180325253244332421016588707628178068007417781929803653363) : ℚ) := by
  unfold recurrence2B5A6
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
    rw [show 32 = 12 +
      20 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_154_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_154_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_155_prefix_zero :
    (∑ x ∈ Finset.range 60,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (155 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (155 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_155_suffix_zero :
    (∑ x ∈ Finset.range 21,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (155 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_155 :
    recurrence2B5A6.coeff 155 =
      ((2190530029337243438149072222747813456100210108172318822034 * 10 ^ 70 +
        3093138959642922381599474934387833551744996247056539142212472316851704) : ℚ) := by
  unfold recurrence2B5A6
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
    rw [show 32 = 11 +
      21 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_155_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_155_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_156_prefix_zero :
    (∑ x ∈ Finset.range 61,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (156 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (156 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_156_suffix_zero :
    (∑ x ∈ Finset.range 22,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (156 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_156 :
    recurrence2B5A6.coeff 156 =
      -((208293487410504682490436237340270878248850828576109700316 * 10 ^ 70 +
        2124741426931850076693474252599669507546358648230512382690268768481174) : ℚ) := by
  unfold recurrence2B5A6
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
    rw [show 32 = 10 +
      22 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_156_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_156_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_157_prefix_zero :
    (∑ x ∈ Finset.range 62,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (157 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (157 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_157_suffix_zero :
    (∑ x ∈ Finset.range 23,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (157 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_157 :
    recurrence2B5A6.coeff 157 =
      -((683269246255285434533504978884653843284932920879269403270 * 10 ^ 70 +
        6132406700203077381408118011304734692307447174233993371540432394516458) : ℚ) := by
  unfold recurrence2B5A6
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
    rw [show 32 = 9 +
      23 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_157_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_157_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_158_prefix_zero :
    (∑ x ∈ Finset.range 63,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (158 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (158 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_158_suffix_zero :
    (∑ x ∈ Finset.range 24,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (158 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_158 :
    recurrence2B5A6.coeff 158 =
      ((888217143171099649387916922625681769505215265675226369101 * 10 ^ 70 +
        8535987109907558884678685907071145078612543109546741975474498889093071) : ℚ) := by
  unfold recurrence2B5A6
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
    rw [show 32 = 8 +
      24 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_158_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_158_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_159_prefix_zero :
    (∑ x ∈ Finset.range 64,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (159 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (159 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_159_suffix_zero :
    (∑ x ∈ Finset.range 25,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (159 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_159 :
    recurrence2B5A6.coeff 159 =
      -((755533291351298597718891163441562557952851267183794347561 * 10 ^ 70 +
        2856803945729201411607183928687648355467035936448123498106394889069661) : ℚ) := by
  unfold recurrence2B5A6
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
    rw [show 32 = 7 +
      25 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_159_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_159_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_160_prefix_zero :
    (∑ x ∈ Finset.range 65,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (160 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (160 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_160_suffix_zero :
    (∑ x ∈ Finset.range 26,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (160 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_160 :
    recurrence2B5A6.coeff 160 =
      ((520767046583138081300293871662100806848417075684347277537 * 10 ^ 70 +
        2572940043723122978483432138550322692201695447572055943211083810245884) : ℚ) := by
  unfold recurrence2B5A6
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
    rw [show 32 = 6 +
      26 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_160_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_160_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_161_prefix_zero :
    (∑ x ∈ Finset.range 66,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (161 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (161 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_161_suffix_zero :
    (∑ x ∈ Finset.range 27,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (161 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_161 :
    recurrence2B5A6.coeff 161 =
      -((307168500400924906746556667234979247733354713280913887159 * 10 ^ 70 +
        0709302317554714157556746244075224048078894664793914761513310706886311) : ℚ) := by
  unfold recurrence2B5A6
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
    rw [show 32 = 5 +
      27 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_161_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_161_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_162_prefix_zero :
    (∑ x ∈ Finset.range 67,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (162 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (162 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_162_suffix_zero :
    (∑ x ∈ Finset.range 28,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (162 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_162 :
    recurrence2B5A6.coeff 162 =
      ((157162689700482792581269292935907768275034842606997202297 * 10 ^ 70 +
        4146631701788964830753118806918297931589777990125503705918835603381559) : ℚ) := by
  unfold recurrence2B5A6
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
    rw [show 32 = 4 +
      28 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_162_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_162_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_163_prefix_zero :
    (∑ x ∈ Finset.range 68,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (163 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (163 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_163_suffix_zero :
    (∑ x ∈ Finset.range 29,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (163 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_163 :
    recurrence2B5A6.coeff 163 =
      -((69042369644045785568185346534032639399009216213763753468 * 10 ^ 70 +
        9419223579125783232374694774354948783020274398237196937758054457460636) : ℚ) := by
  unfold recurrence2B5A6
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
    rw [show 32 = 3 +
      29 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_163_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_163_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_164_prefix_zero :
    (∑ x ∈ Finset.range 69,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (164 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (164 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_164_suffix_zero :
    (∑ x ∈ Finset.range 30,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (164 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_164 :
    recurrence2B5A6.coeff 164 =
      ((24908192544710496233092172795309347369680829271167950030 * 10 ^ 70 +
        7176788661057311035551202820900634623229674109365233946173771188095791) : ℚ) := by
  unfold recurrence2B5A6
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
    rw [show 32 = 2 +
      30 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_164_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_164_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_165_prefix_zero :
    (∑ x ∈ Finset.range 70,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (165 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (165 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_165_suffix_zero :
    (∑ x ∈ Finset.range 31,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (165 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_165 :
    recurrence2B5A6.coeff 165 =
      -((6311977307240465951205834311617631266889534277193947745 * 10 ^ 70 +
        4355530723600114888821213866584199665498819536473346820670378512687097) : ℚ) := by
  unfold recurrence2B5A6
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
    rw [show 32 = 1 +
      31 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_165_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_165_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_166_prefix_zero :
    (∑ x ∈ Finset.range 71,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (166 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (166 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_166_suffix_zero :
    (∑ x ∈ Finset.range 32,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (166 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_166 :
    recurrence2B5A6.coeff 166 =
      ((122520971693433166718603503821170235981432232769347873 * 10 ^ 70 +
        1670964145179527964887146532952005884295029584750646030374738250142346) : ℚ) := by
  unfold recurrence2B5A6
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
  rw [recurrence2B5A6_coeff_166_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_166_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_167_prefix_zero :
    (∑ x ∈ Finset.range 72,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (167 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (167 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_167_suffix_zero :
    (∑ x ∈ Finset.range 33,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (167 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_167 :
    recurrence2B5A6.coeff 167 =
      ((1120241249634827447695471733162118258917227557572746691 * 10 ^ 70 +
        7541834596164274601010981194662404238234846094678430946375368344329231) : ℚ) := by
  unfold recurrence2B5A6
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
    rw [show 64 = 31 +
      33 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_167_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_167_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_168_prefix_zero :
    (∑ x ∈ Finset.range 73,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (168 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (168 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_168_suffix_zero :
    (∑ x ∈ Finset.range 34,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (168 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_168 :
    recurrence2B5A6.coeff 168 =
      -((891715695625811432431483935562263580223899413209988982 * 10 ^ 70 +
        5614479202507224664521245260277354226338756359291107526672333588697930) : ℚ) := by
  unfold recurrence2B5A6
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
    rw [show 64 = 30 +
      34 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_168_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_168_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_169_prefix_zero :
    (∑ x ∈ Finset.range 74,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (169 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (169 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_169_suffix_zero :
    (∑ x ∈ Finset.range 35,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (169 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_169 :
    recurrence2B5A6.coeff 169 =
      ((479153845674924322536683071286811466255982410353663282 * 10 ^ 70 +
        7026701177069466746359724880923889569048553345118977862466940095611901) : ℚ) := by
  unfold recurrence2B5A6
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
    rw [show 64 = 29 +
      35 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_169_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_169_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_170_prefix_zero :
    (∑ x ∈ Finset.range 75,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (170 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (170 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_170_suffix_zero :
    (∑ x ∈ Finset.range 36,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (170 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_170 :
    recurrence2B5A6.coeff 170 =
      -((206235833317602416685596746723470711882588807359233284 * 10 ^ 70 +
        0561481815909494665253922858452520297514427361079780179175259416644521) : ℚ) := by
  unfold recurrence2B5A6
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
    rw [show 64 = 28 +
      36 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_170_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_170_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_171_prefix_zero :
    (∑ x ∈ Finset.range 76,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (171 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (171 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_171_suffix_zero :
    (∑ x ∈ Finset.range 37,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (171 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_171 :
    recurrence2B5A6.coeff 171 =
      ((73804134542800090405423702245237875628766995415821580 * 10 ^ 70 +
        8063894252254607810565424143013895588432578011975454088777419773530803) : ℚ) := by
  unfold recurrence2B5A6
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
    rw [show 64 = 27 +
      37 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_171_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_171_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_172_prefix_zero :
    (∑ x ∈ Finset.range 77,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (172 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (172 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_172_suffix_zero :
    (∑ x ∈ Finset.range 38,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (172 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_172 :
    recurrence2B5A6.coeff 172 =
      -((21707745651788686657493789569536690353546960667732890 * 10 ^ 70 +
        2297034975459372995345987834371964799717988354278626542342007244613569) : ℚ) := by
  unfold recurrence2B5A6
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
    rw [show 64 = 26 +
      38 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_172_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_172_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_173_prefix_zero :
    (∑ x ∈ Finset.range 78,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (173 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (173 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_173_suffix_zero :
    (∑ x ∈ Finset.range 39,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (173 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_173 :
    recurrence2B5A6.coeff 173 =
      ((4860184785282559133287938746409535094505588662012754 * 10 ^ 70 +
        9626355488049212473184857520456301910919108464469019990049182265878338) : ℚ) := by
  unfold recurrence2B5A6
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
    rw [show 64 = 25 +
      39 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_173_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_173_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_174_prefix_zero :
    (∑ x ∈ Finset.range 79,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (174 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (174 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_174_suffix_zero :
    (∑ x ∈ Finset.range 40,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (174 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_174 :
    recurrence2B5A6.coeff 174 =
      -((562208379012828988172393319399882964092857774612970 * 10 ^ 70 +
        6634559073963576265896021995583413778793875063513077315372152799381214) : ℚ) := by
  unfold recurrence2B5A6
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
    rw [show 64 = 24 +
      40 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_174_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_174_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_175_prefix_zero :
    (∑ x ∈ Finset.range 80,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (175 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (175 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_175_suffix_zero :
    (∑ x ∈ Finset.range 41,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (175 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_175 :
    recurrence2B5A6.coeff 175 =
      -((154412297419670876431387381566375899592038321330392 * 10 ^ 70 +
        7307563770286921474952331708883358656073013152619784829315130701055860) : ℚ) := by
  unfold recurrence2B5A6
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
    rw [show 64 = 23 +
      41 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_175_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_175_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_176_prefix_zero :
    (∑ x ∈ Finset.range 81,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (176 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (176 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_176_suffix_zero :
    (∑ x ∈ Finset.range 42,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (176 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_176 :
    recurrence2B5A6.coeff 176 =
      ((131502936900234025172193508256449059122428964587862 * 10 ^ 70 +
        4534028652187925475183960369081561003787318170997104180122138286707514) : ℚ) := by
  unfold recurrence2B5A6
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
    rw [show 64 = 22 +
      42 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_176_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_176_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_177_prefix_zero :
    (∑ x ∈ Finset.range 82,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (177 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (177 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_177_suffix_zero :
    (∑ x ∈ Finset.range 43,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (177 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_177 :
    recurrence2B5A6.coeff 177 =
      -((54013815206540870754159365354752165397121472420438 * 10 ^ 70 +
        1554583315324996039730079204968070332388147063700992084293877285484521) : ℚ) := by
  unfold recurrence2B5A6
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
    rw [show 64 = 21 +
      43 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_177_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_177_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_178_prefix_zero :
    (∑ x ∈ Finset.range 83,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (178 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (178 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_178_suffix_zero :
    (∑ x ∈ Finset.range 44,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (178 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_178 :
    recurrence2B5A6.coeff 178 =
      ((16293090375914160093864086556986711585048019915436 * 10 ^ 70 +
        1729134864447877590064676113960173084899599085898035605048345656041281) : ℚ) := by
  unfold recurrence2B5A6
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
    rw [show 64 = 20 +
      44 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_178_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_178_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_179_prefix_zero :
    (∑ x ∈ Finset.range 84,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (179 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (179 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_179_suffix_zero :
    (∑ x ∈ Finset.range 45,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (179 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_179 :
    recurrence2B5A6.coeff 179 =
      -((3825161769058816263098103900963431382173392794092 * 10 ^ 70 +
        8324400496787751379597888787752362254269344895051304625919113791641885) : ℚ) := by
  unfold recurrence2B5A6
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
    rw [show 64 = 19 +
      45 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_179_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_179_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_180_prefix_zero :
    (∑ x ∈ Finset.range 85,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (180 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (180 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_180_suffix_zero :
    (∑ x ∈ Finset.range 46,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (180 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_180 :
    recurrence2B5A6.coeff 180 =
      ((667929722383432105648171243313851300643370433704 * 10 ^ 70 +
        6338787025526484817396651660958396626070863949359256692471441368724543) : ℚ) := by
  unfold recurrence2B5A6
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
    rw [show 64 = 18 +
      46 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_180_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_180_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_181_prefix_zero :
    (∑ x ∈ Finset.range 86,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (181 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (181 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_181_suffix_zero :
    (∑ x ∈ Finset.range 47,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (181 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_181 :
    recurrence2B5A6.coeff 181 =
      -((64377891752151302333859506806071388983520111556 * 10 ^ 70 +
        6978521057436618895924055086461499208048927533095718431700276177858121) : ℚ) := by
  unfold recurrence2B5A6
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
    rw [show 64 = 17 +
      47 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_181_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_181_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_182_prefix_zero :
    (∑ x ∈ Finset.range 87,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (182 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (182 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_182_suffix_zero :
    (∑ x ∈ Finset.range 48,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (182 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_182 :
    recurrence2B5A6.coeff 182 =
      -((7813261889507937113842875614988552612854110866 * 10 ^ 70 +
        5741374039493513695771312525629134782019256541212048835943524492898971) : ℚ) := by
  unfold recurrence2B5A6
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
    rw [show 64 = 16 +
      48 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_182_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_182_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_183_prefix_zero :
    (∑ x ∈ Finset.range 88,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (183 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (183 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_183_suffix_zero :
    (∑ x ∈ Finset.range 49,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (183 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_183 :
    recurrence2B5A6.coeff 183 =
      ((5597441094407044582119292741379008637303156451 * 10 ^ 70 +
        2835005001558599613227254917539271362389195477239919977009301056750471) : ℚ) := by
  unfold recurrence2B5A6
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
    rw [show 64 = 15 +
      49 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_183_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_183_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_184_prefix_zero :
    (∑ x ∈ Finset.range 89,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (184 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (184 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_184_suffix_zero :
    (∑ x ∈ Finset.range 50,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (184 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_184 :
    recurrence2B5A6.coeff 184 =
      -((1576897651833143222450795635519530309815810716 * 10 ^ 70 +
        2123237850704447416338202722461186974922164275912429693937743387100795) : ℚ) := by
  unfold recurrence2B5A6
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
    rw [show 64 = 14 +
      50 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_184_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_184_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_185_prefix_zero :
    (∑ x ∈ Finset.range 90,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (185 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (185 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_185_suffix_zero :
    (∑ x ∈ Finset.range 51,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (185 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_185 :
    recurrence2B5A6.coeff 185 =
      ((301481699130115216274336614218152019058761888 * 10 ^ 70 +
        0570751968659522406734490170403825354729721662092854947171190141483297) : ℚ) := by
  unfold recurrence2B5A6
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
    rw [show 64 = 13 +
      51 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_185_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_185_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_186_prefix_zero :
    (∑ x ∈ Finset.range 91,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (186 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (186 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_186_suffix_zero :
    (∑ x ∈ Finset.range 52,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (186 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_186 :
    recurrence2B5A6.coeff 186 =
      -((39767300556200834787151499444798353542057085 * 10 ^ 70 +
        3756587419712965796151928569973437409900549624352932716880083049927106) : ℚ) := by
  unfold recurrence2B5A6
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
    rw [show 64 = 12 +
      52 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_186_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_186_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_187_prefix_zero :
    (∑ x ∈ Finset.range 92,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (187 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (187 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_187_suffix_zero :
    (∑ x ∈ Finset.range 53,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (187 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_187 :
    recurrence2B5A6.coeff 187 =
      ((2604747321226694304942050504226166530440640 * 10 ^ 70 +
        3551920125117519691580797220709481951588036657427933617148583771214377) : ℚ) := by
  unfold recurrence2B5A6
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
    rw [show 64 = 11 +
      53 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_187_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_187_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_188_prefix_zero :
    (∑ x ∈ Finset.range 93,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (188 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (188 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_188_suffix_zero :
    (∑ x ∈ Finset.range 54,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (188 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_188 :
    recurrence2B5A6.coeff 188 =
      ((302221171343532743121979638714362520264833 * 10 ^ 70 +
        3200363844491636568134322025383050309220501427363654177293105846121254) : ℚ) := by
  unfold recurrence2B5A6
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
    rw [show 64 = 10 +
      54 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_188_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_188_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_189_prefix_zero :
    (∑ x ∈ Finset.range 94,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (189 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (189 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_189_suffix_zero :
    (∑ x ∈ Finset.range 55,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (189 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_189 :
    recurrence2B5A6.coeff 189 =
      -((126341740952666921184752762969476454869110 * 10 ^ 70 +
        8924821917899642804678016656157066640306079409736458957310809075282107) : ℚ) := by
  unfold recurrence2B5A6
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
    rw [show 64 = 9 +
      55 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_189_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_189_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_190_prefix_zero :
    (∑ x ∈ Finset.range 95,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (190 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (190 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_190_suffix_zero :
    (∑ x ∈ Finset.range 56,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (190 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_190 :
    recurrence2B5A6.coeff 190 =
      ((21655948538343665712073709124632053302532 * 10 ^ 70 +
        3639756893814728776314476050882614354741701987912069916353002586546190) : ℚ) := by
  unfold recurrence2B5A6
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
    rw [show 64 = 8 +
      56 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_190_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_190_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_191_prefix_zero :
    (∑ x ∈ Finset.range 96,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (191 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (191 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_191_suffix_zero :
    (∑ x ∈ Finset.range 57,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (191 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_191 :
    recurrence2B5A6.coeff 191 =
      -((2238399925325495193109752483226732225559 * 10 ^ 70 +
        5242804064696556816811844139792077580077080098320038324401245920123611) : ℚ) := by
  unfold recurrence2B5A6
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
    rw [show 64 = 7 +
      57 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_191_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_191_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_192_prefix_zero :
    (∑ x ∈ Finset.range 97,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (192 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (192 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_192_suffix_zero :
    (∑ x ∈ Finset.range 58,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (192 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_192 :
    recurrence2B5A6.coeff 192 =
      ((100192504675072601022132672261941272153 * 10 ^ 70 +
        4421470773431346123137221128823525061006796366924939108488900520445131) : ℚ) := by
  unfold recurrence2B5A6
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
    rw [show 64 = 6 +
      58 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_192_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_192_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_193_prefix_zero :
    (∑ x ∈ Finset.range 98,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (193 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (193 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_193_suffix_zero :
    (∑ x ∈ Finset.range 59,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (193 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_193 :
    recurrence2B5A6.coeff 193 =
      ((10612341784811957542948807966871792189 * 10 ^ 70 +
        7050788433393927137913623167808975825091400254437121937637500651232184) : ℚ) := by
  unfold recurrence2B5A6
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
    rw [show 64 = 5 +
      59 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_193_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_193_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_194_prefix_zero :
    (∑ x ∈ Finset.range 99,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (194 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (194 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_194_suffix_zero :
    (∑ x ∈ Finset.range 60,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (194 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_194 :
    recurrence2B5A6.coeff 194 =
      -((2596436452403114198079693668671127128 * 10 ^ 70 +
        2959574556605831401555165645035917485808615396201044064817106488100468) : ℚ) := by
  unfold recurrence2B5A6
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
    rw [show 64 = 4 +
      60 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_194_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_194_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_195_prefix_zero :
    (∑ x ∈ Finset.range 100,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (195 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (195 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_195_suffix_zero :
    (∑ x ∈ Finset.range 61,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (195 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_195 :
    recurrence2B5A6.coeff 195 =
      ((249419936435603285284791281921477055 * 10 ^ 70 +
        2664697717367407211153150220465211173271409072171422237724728480659541) : ℚ) := by
  unfold recurrence2B5A6
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
    rw [show 64 = 3 +
      61 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_195_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_195_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_196_prefix_zero :
    (∑ x ∈ Finset.range 101,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (196 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (196 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_196_suffix_zero :
    (∑ x ∈ Finset.range 62,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (196 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_196 :
    recurrence2B5A6.coeff 196 =
      -((10091192818589072600418706025916823 * 10 ^ 70 +
        5372289023217327855403494060603398574893058836639574030845371311072859) : ℚ) := by
  unfold recurrence2B5A6
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
    rw [show 64 = 2 +
      62 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_196_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_196_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_197_prefix_zero :
    (∑ x ∈ Finset.range 102,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (197 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (197 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_197_suffix_zero :
    (∑ x ∈ Finset.range 63,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (197 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_197 :
    recurrence2B5A6.coeff 197 =
      -((483516215683355745789656674320164 * 10 ^ 70 +
        4625711777377109375726139007373555362255102931524781934496147137127159) : ℚ) := by
  unfold recurrence2B5A6
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
    rw [show 64 = 1 +
      63 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_197_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_197_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_198_prefix_zero :
    (∑ x ∈ Finset.range 103,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (198 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (198 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_198_suffix_zero :
    (∑ x ∈ Finset.range 64,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (198 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_198 :
    recurrence2B5A6.coeff 198 =
      ((92896189412938660772686693766652 * 10 ^ 70 +
        3417968821828964046790311059453167260877197917875845205395329183310470) : ℚ) := by
  unfold recurrence2B5A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 199 = 103 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_198_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_198_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_199_prefix_zero :
    (∑ x ∈ Finset.range 104,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (199 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (199 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_199_suffix_zero :
    (∑ x ∈ Finset.range 65,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (199 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_199 :
    recurrence2B5A6.coeff 199 =
      -((5034629359224923274264301358832 * 10 ^ 70 +
        7347784534501821216660526403741648557632034474512252211043230426929362) : ℚ) := by
  unfold recurrence2B5A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 200 = 104 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 31 +
      65 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_199_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_199_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_200_prefix_zero :
    (∑ x ∈ Finset.range 105,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (200 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (200 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_200_suffix_zero :
    (∑ x ∈ Finset.range 66,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (200 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_200 :
    recurrence2B5A6.coeff 200 =
      ((18826644932617963824146300896 * 10 ^ 70 +
        6499985828457793275235487730435160641030347011880488977002768418457409) : ℚ) := by
  unfold recurrence2B5A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 201 = 105 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 30 +
      66 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_200_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_200_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_201_prefix_zero :
    (∑ x ∈ Finset.range 106,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (201 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (201 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_201_suffix_zero :
    (∑ x ∈ Finset.range 67,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (201 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_201 :
    recurrence2B5A6.coeff 201 =
      ((11586179749058206792664801765 * 10 ^ 70 +
        2731760035672117407057117608946356915606382168513324677808564650556073) : ℚ) := by
  unfold recurrence2B5A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 202 = 106 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 29 +
      67 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_201_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_201_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_202_prefix_zero :
    (∑ x ∈ Finset.range 107,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (202 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (202 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_202_suffix_zero :
    (∑ x ∈ Finset.range 68,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (202 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_202 :
    recurrence2B5A6.coeff 202 =
      -((505044280677479482679271208 * 10 ^ 70 +
        9615585669799697301975902311518637001554577432122449583801577522908950) : ℚ) := by
  unfold recurrence2B5A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 203 = 107 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 28 +
      68 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_202_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_202_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_203_prefix_zero :
    (∑ x ∈ Finset.range 108,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (203 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (203 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_203_suffix_zero :
    (∑ x ∈ Finset.range 69,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (203 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_203 :
    recurrence2B5A6.coeff 203 =
      -((719450407007150669698726 * 10 ^ 70 +
        4365020648602119052299435707906110399733277693674203748467510145028637) : ℚ) := by
  unfold recurrence2B5A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 204 = 108 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 27 +
      69 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_203_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_203_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_204_prefix_zero :
    (∑ x ∈ Finset.range 109,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (204 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (204 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_204_suffix_zero :
    (∑ x ∈ Finset.range 70,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (204 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_204 :
    recurrence2B5A6.coeff 204 =
      ((528046615729000389457662 * 10 ^ 70 +
        5755622265240973861502531425861923442913083002434536629600851713535166) : ℚ) := by
  unfold recurrence2B5A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 205 = 109 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 26 +
      70 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_204_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_204_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_205_prefix_zero :
    (∑ x ∈ Finset.range 110,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (205 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (205 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_205_suffix_zero :
    (∑ x ∈ Finset.range 71,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (205 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_205 :
    recurrence2B5A6.coeff 205 =
      -((7617586486932188576880 * 10 ^ 70 +
        0948874366480435363255027821537952867865037581736626782555249107542385) : ℚ) := by
  unfold recurrence2B5A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 206 = 110 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 25 +
      71 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_205_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_205_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_206_prefix_zero :
    (∑ x ∈ Finset.range 111,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (206 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (206 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_206_suffix_zero :
    (∑ x ∈ Finset.range 72,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (206 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_206 :
    recurrence2B5A6.coeff 206 =
      -((175926196577227049959 * 10 ^ 70 +
        8671893781778350890669632836629414418581573713778416350129747808018787) : ℚ) := by
  unfold recurrence2B5A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 207 = 111 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 24 +
      72 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_206_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_206_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_207_prefix_zero :
    (∑ x ∈ Finset.range 112,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (207 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (207 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_207_suffix_zero :
    (∑ x ∈ Finset.range 73,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (207 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_207 :
    recurrence2B5A6.coeff 207 =
      ((3290419657336534073 * 10 ^ 70 +
        1257958659154329208253443992529517706711345785926722253505669671992716) : ℚ) := by
  unfold recurrence2B5A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 208 = 112 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 23 +
      73 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_207_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_207_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_208_prefix_zero :
    (∑ x ∈ Finset.range 113,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (208 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (208 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_208_suffix_zero :
    (∑ x ∈ Finset.range 74,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (208 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_208 :
    recurrence2B5A6.coeff 208 =
      ((26525765013690811 * 10 ^ 70 +
        5633923113597357439146771189607236055117268228034813049384872630548752) : ℚ) := by
  unfold recurrence2B5A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 209 = 113 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 22 +
      74 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_208_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_208_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_209_prefix_zero :
    (∑ x ∈ Finset.range 114,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (209 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (209 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_209_suffix_zero :
    (∑ x ∈ Finset.range 75,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (209 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_209 :
    recurrence2B5A6.coeff 209 =
      -((413208691665808 * 10 ^ 70 +
        9834987160521264234161963816095081993483784027231427844009162996844332) : ℚ) := by
  unfold recurrence2B5A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 210 = 114 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 21 +
      75 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_209_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_209_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_210_prefix_zero :
    (∑ x ∈ Finset.range 115,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (210 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (210 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_210_suffix_zero :
    (∑ x ∈ Finset.range 76,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (210 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_210 :
    recurrence2B5A6.coeff 210 =
      -((2308775710790 * 10 ^ 70 +
        3787076629380299654538445120040204682614022434483132768223910443566492) : ℚ) := by
  unfold recurrence2B5A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 211 = 115 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 20 +
      76 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_210_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_210_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_211_prefix_zero :
    (∑ x ∈ Finset.range 116,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (211 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (211 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_211_suffix_zero :
    (∑ x ∈ Finset.range 77,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (211 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_211 :
    recurrence2B5A6.coeff 211 =
      ((17669729934 * 10 ^ 70 +
        5826829448701052860196770326475099334448476155324106825205089624743924) : ℚ) := by
  unfold recurrence2B5A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 212 = 116 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 19 +
      77 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_211_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_211_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_212_prefix_zero :
    (∑ x ∈ Finset.range 117,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (212 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (212 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_212_suffix_zero :
    (∑ x ∈ Finset.range 78,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (212 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_212 :
    recurrence2B5A6.coeff 212 =
      ((89921022 * 10 ^ 70 +
        0732987870823816054371313625342272042158706106881973138687886112439212) : ℚ) := by
  unfold recurrence2B5A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 213 = 117 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 18 +
      78 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_212_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_212_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_213_prefix_zero :
    (∑ x ∈ Finset.range 118,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (213 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (213 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_213_suffix_zero :
    (∑ x ∈ Finset.range 79,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (213 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_213 :
    recurrence2B5A6.coeff 213 =
      -((287146 * 10 ^ 70 +
        5579345454568344355515567261703240265030372260390051779332915585468812) : ℚ) := by
  unfold recurrence2B5A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 214 = 118 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 17 +
      79 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_213_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_213_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_214_prefix_zero :
    (∑ x ∈ Finset.range 119,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (214 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (214 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_214_suffix_zero :
    (∑ x ∈ Finset.range 80,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (214 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_214 :
    recurrence2B5A6.coeff 214 =
      -((1314 * 10 ^ 70 +
        4073973700480964046569418925398588319943153247395331554220214235216825) : ℚ) := by
  unfold recurrence2B5A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 215 = 119 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 16 +
      80 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_214_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_214_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_215_prefix_zero :
    (∑ x ∈ Finset.range 120,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (215 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (215 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_215_suffix_zero :
    (∑ x ∈ Finset.range 81,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (215 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_215 :
    recurrence2B5A6.coeff 215 =
      ((2 * 10 ^ 70 +
        4654137165483896561600070961803398528392126344112076430343097412079616) : ℚ) := by
  unfold recurrence2B5A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 216 = 120 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 15 +
      81 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_215_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_215_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_216_prefix_zero :
    (∑ x ∈ Finset.range 121,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (216 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (216 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_216_suffix_zero :
    (∑ x ∈ Finset.range 82,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (216 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_216 :
    recurrence2B5A6.coeff 216 =
      (76009889025658934244292396766375998545648963184867802738203436007732 : ℚ) := by
  unfold recurrence2B5A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 217 = 121 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 14 +
      82 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_216_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_216_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_217_prefix_zero :
    (∑ x ∈ Finset.range 122,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (217 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (217 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_217_suffix_zero :
    (∑ x ∈ Finset.range 83,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (217 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_217 :
    recurrence2B5A6.coeff 217 =
      (-126514700701944697320757962662840619824600259027243913635868449596 : ℚ) := by
  unfold recurrence2B5A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 218 = 122 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 13 +
      83 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_217_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_217_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_218_prefix_zero :
    (∑ x ∈ Finset.range 123,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (218 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (218 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_218_suffix_zero :
    (∑ x ∈ Finset.range 84,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (218 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_218 :
    recurrence2B5A6.coeff 218 =
      (-132827894524043477466213019899594939341439474931724564246045460 : ℚ) := by
  unfold recurrence2B5A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 219 = 123 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 12 +
      84 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_218_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_218_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_219_prefix_zero :
    (∑ x ∈ Finset.range 124,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (219 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (219 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_219_suffix_zero :
    (∑ x ∈ Finset.range 85,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (219 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_219 :
    recurrence2B5A6.coeff 219 =
      (247903174913007753342138830410187476382045041194203116007127 : ℚ) := by
  unfold recurrence2B5A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 220 = 124 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 11 +
      85 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_219_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_219_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_220_prefix_zero :
    (∑ x ∈ Finset.range 125,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (220 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (220 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_220_suffix_zero :
    (∑ x ∈ Finset.range 86,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (220 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_220 :
    recurrence2B5A6.coeff 220 =
      (-13574613626135994902360235302546928417931660176350449347 : ℚ) := by
  unfold recurrence2B5A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 221 = 125 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 10 +
      86 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_220_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_220_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_221_prefix_zero :
    (∑ x ∈ Finset.range 126,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (221 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (221 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_221_suffix_zero :
    (∑ x ∈ Finset.range 87,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (221 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_221 :
    recurrence2B5A6.coeff 221 =
      (-57563639112097116561954567451077295652677154996655375 : ℚ) := by
  unfold recurrence2B5A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 222 = 126 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 9 +
      87 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_221_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_221_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_222_prefix_zero :
    (∑ x ∈ Finset.range 127,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (222 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (222 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_222_suffix_zero :
    (∑ x ∈ Finset.range 88,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (222 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_222 :
    recurrence2B5A6.coeff 222 =
      (9068578571047909891010716792409519624685283159228 : ℚ) := by
  unfold recurrence2B5A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 223 = 127 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 8 +
      88 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_222_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_222_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2B5A6_coeff_223_prefix_zero :
    (∑ x ∈ Finset.range 128,
      remainder3Coefficient5.coeff x * remainder2Coefficient6.coeff (223 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (223 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A6_coeff_223_suffix_zero :
    (∑ x ∈ Finset.range 89,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient6.coeff (223 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A6_coeff_223 :
    recurrence2B5A6.coeff 223 =
      (395517672689918353189157199637154378164600507 : ℚ) := by
  unfold recurrence2B5A6
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 224 = 128 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 7 +
      89 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A6_coeff_223_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A6_coeff_223_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
