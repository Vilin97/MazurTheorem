/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB5
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupA5
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB5A5Part0Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: B5A5 coefficient convolution

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
  recurrence2A5_coeff_0
  recurrence2A5_coeff_1
  recurrence2A5_coeff_2
  recurrence2A5_coeff_3
  recurrence2A5_coeff_4
  recurrence2A5_coeff_5
  recurrence2A5_coeff_6
  recurrence2A5_coeff_7
  recurrence2A5_coeff_8
  recurrence2A5_coeff_9
  recurrence2A5_coeff_10
  recurrence2A5_coeff_11
  recurrence2A5_coeff_12
  recurrence2A5_coeff_13
  recurrence2A5_coeff_14
  recurrence2A5_coeff_15
  recurrence2A5_coeff_16
  recurrence2A5_coeff_17
  recurrence2A5_coeff_18
  recurrence2A5_coeff_19
  recurrence2A5_coeff_20
  recurrence2A5_coeff_21
  recurrence2A5_coeff_22
  recurrence2A5_coeff_23
  recurrence2A5_coeff_24
  recurrence2A5_coeff_25
  recurrence2A5_coeff_26
  recurrence2A5_coeff_27
  recurrence2A5_coeff_28
  recurrence2A5_coeff_29
  recurrence2A5_coeff_30
  recurrence2A5_coeff_31
  recurrence2A5_coeff_32
  recurrence2A5_coeff_33
  recurrence2A5_coeff_34
  recurrence2A5_coeff_35
  recurrence2A5_coeff_36
  recurrence2A5_coeff_37
  recurrence2A5_coeff_38
  recurrence2A5_coeff_39
  recurrence2A5_coeff_40
  recurrence2A5_coeff_41
  recurrence2A5_coeff_42
  recurrence2A5_coeff_43
  recurrence2A5_coeff_44
  recurrence2A5_coeff_45
  recurrence2A5_coeff_46
  recurrence2A5_coeff_47
  recurrence2A5_coeff_48
  recurrence2A5_coeff_49
  recurrence2A5_coeff_50
  recurrence2A5_coeff_51
  recurrence2A5_coeff_52
  recurrence2A5_coeff_53
  recurrence2A5_coeff_54
  recurrence2A5_coeff_55
  recurrence2A5_coeff_56
  recurrence2A5_coeff_57
  recurrence2A5_coeff_58
  recurrence2A5_coeff_59
  recurrence2A5_coeff_60
  recurrence2A5_coeff_61
  recurrence2A5_coeff_62
  recurrence2A5_coeff_63
  recurrence2A5_coeff_64
  recurrence2A5_coeff_65
  recurrence2A5_coeff_66
  recurrence2A5_coeff_67
  recurrence2A5_coeff_68
  recurrence2A5_coeff_69
  recurrence2A5_coeff_70
  recurrence2A5_coeff_71
  recurrence2A5_coeff_72
  recurrence2A5_coeff_73
  recurrence2A5_coeff_74
  recurrence2A5_coeff_75
  recurrence2A5_coeff_76
  recurrence2A5_coeff_77
  recurrence2A5_coeff_78
  recurrence2A5_coeff_79
  recurrence2A5_coeff_80
  recurrence2A5_coeff_81
  recurrence2A5_coeff_82
  recurrence2A5_coeff_83
  recurrence2A5_coeff_84
  recurrence2A5_coeff_85
  recurrence2A5_coeff_86
  recurrence2A5_coeff_87
  recurrence2A5_coeff_88
  recurrence2A5_coeff_89
  recurrence2A5_coeff_90
  recurrence2A5_coeff_91
  recurrence2A5_coeff_92
  recurrence2A5_coeff_93
  recurrence2A5_coeff_94
  recurrence2A5_coeff_95
  recurrence2A5_coeff_96
  recurrence2A5_coeff_97
  recurrence2A5_coeff_98

theorem recurrence2B5A5_coeff_0 :
    recurrence2B5A5.coeff 0 =
      (-512 : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 1 = 0 +
    1 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 1 = 1 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_1 :
    recurrence2B5A5.coeff 1 =
      (-196128 : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 2 = 0 +
    2 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 2 = 2 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_2 :
    recurrence2B5A5.coeff 2 =
      (-7055788656 : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 3 = 0 +
    3 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_3 :
    recurrence2B5A5.coeff 3 =
      (-3612890666128 : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 4 = 0 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_4 :
    recurrence2B5A5.coeff 4 =
      (76638530985305740 : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 5 = 0 +
    5 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 5 = 5 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_5 :
    recurrence2B5A5.coeff 5 =
      (-49420793424090909278 : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 6 = 0 +
    6 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 6 = 6 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_6 :
    recurrence2B5A5.coeff 6 =
      (40234244025010885088378 : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 7 = 0 +
    7 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_7 :
    recurrence2B5A5.coeff 7 =
      (-16364375868967617715366912 : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 8 = 0 +
    8 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 8 = 8 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_8 :
    recurrence2B5A5.coeff 8 =
      (3540413305976529654299628632 : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 9 = 0 +
    9 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 9 = 9 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_9 :
    recurrence2B5A5.coeff 9 =
      (-488649306782244962367000456098 : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 10 = 0 +
    10 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 10 = 10 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_10 :
    recurrence2B5A5.coeff 10 =
      (27413141233688613713804505773149 : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 11 = 0 +
    11 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 11 = 11 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_11 :
    recurrence2B5A5.coeff 11 =
      (2078138115228199855230217348907956 : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 12 = 0 +
    12 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 12 = 12 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_12 :
    recurrence2B5A5.coeff 12 =
      (-529718667137543942424510307977277764 : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 13 = 0 +
    13 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_13 :
    recurrence2B5A5.coeff 13 =
      (49129835742333086315485517958639139220 : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 14 = 0 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_14 :
    recurrence2B5A5.coeff 14 =
      (-2515033458837774333831232670196051276410 : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 15 = 0 +
    15 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_15 :
    recurrence2B5A5.coeff 15 =
      (73146675109004402483767023223379711917464 : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 16 = 0 +
    16 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 16 = 16 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_16 :
    recurrence2B5A5.coeff 16 =
      (-994429192235986021562928709112170887819217 : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 17 = 0 +
    17 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_17 :
    recurrence2B5A5.coeff 17 =
      (-11413902045459441908704740518889256713451911 : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 18 = 0 +
    18 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_18 :
    recurrence2B5A5.coeff 18 =
      (2361458920843340991995088066376137404706402264 : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 19 = 0 +
    19 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_19 :
    recurrence2B5A5.coeff 19 =
      (-223337871052218084246323960420046579701798325186 : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 20 = 0 +
    20 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 20 = 20 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_20 :
    recurrence2B5A5.coeff 20 =
      (11990460634996562695988049895446206742107702022823 : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 21 = 0 +
    21 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_21 :
    recurrence2B5A5.coeff 21 =
      (-343838849377239996889606191237786904874793016634394 : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 22 = 0 +
    22 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 22 = 22 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_22 :
    recurrence2B5A5.coeff 22 =
      (3339764398508232132735899709948397381295078501587401 : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 23 = 0 +
    23 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_23 :
    recurrence2B5A5.coeff 23 =
      (84044448916700659153379810250901826600389029688942250 : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 24 = 0 +
    24 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 24 = 24 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_24 :
    recurrence2B5A5.coeff 24 =
      (-1238320231714889262511150558464513461716719766914251627 : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 25 = 0 +
    25 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_25 :
    recurrence2B5A5.coeff 25 =
      (-141089396206125699604979111233618145829382604133536305231 : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 26 = 0 +
    26 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 26 = 26 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_26 :
    recurrence2B5A5.coeff 26 =
      (8144090826294108282046575551249976371968719839357366792889 : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 27 = 0 +
    27 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_27 :
    recurrence2B5A5.coeff 27 =
      (-247034177303386705018466872810404661751311596489844379007078 : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 28 = 0 +
    28 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 28 = 28 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_28 :
    recurrence2B5A5.coeff 28 =
      (5509518452187685069728122817415103964146228013831050078780499 : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 29 = 0 +
    29 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 29 = 29 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_29 :
    recurrence2B5A5.coeff 29 =
      (-106304640900748874444981514460756869131722284206216467552195115 : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 30 = 0 +
    30 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 30 = 30 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_30 :
    recurrence2B5A5.coeff 30 =
      (1949698292728179051563636383213056763217236508321406254953500406 : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 31 = 0 +
    31 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 31 = 31 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_31 :
    recurrence2B5A5.coeff 31 =
      (-33666377149688577570885822714034223630435090640848285267171847112 : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 32 = 0 +
    32 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_32 :
    recurrence2B5A5.coeff 32 =
      (502112714783096507034788594249026839013515544108483929667799440890 : ℚ) := by
  unfold recurrence2B5A5
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
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_33 :
    recurrence2B5A5.coeff 33 =
      (-5698999690180563856610771025438848654577321482072508688712432089482 : ℚ) := by
  unfold recurrence2B5A5
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
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_34 :
    recurrence2B5A5.coeff 34 =
      (33757215789350542260114290077277540257179546617911581621595183273501 : ℚ) := by
  unfold recurrence2B5A5
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
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_35 :
    recurrence2B5A5.coeff 35 =
      (393353013776651175946970386105279731890185261193103006583944928668829 : ℚ) := by
  unfold recurrence2B5A5
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
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_36 :
    recurrence2B5A5.coeff 36 =
      -((1 * 10 ^ 70 +
        7294456461931462787302965215573458925677000150672914281851012643274106) : ℚ) := by
  unfold recurrence2B5A5
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
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_37 :
    recurrence2B5A5.coeff 37 =
      ((36 * 10 ^ 70 +
        6801165073762642670964967731412479538933435301708975512002423386240324) : ℚ) := by
  unfold recurrence2B5A5
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
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_38 :
    recurrence2B5A5.coeff 38 =
      -((611 * 10 ^ 70 +
        5619133074897808933740127140061069797545235432885064410557575197981869) : ℚ) := by
  unfold recurrence2B5A5
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
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_39 :
    recurrence2B5A5.coeff 39 =
      ((8850 * 10 ^ 70 +
        2516000292433209229048961645294594982018060347785010687517011538810560) : ℚ) := by
  unfold recurrence2B5A5
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
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_40 :
    recurrence2B5A5.coeff 40 =
      -((114566 * 10 ^ 70 +
        8268526375944511145050611313047211002081493140972759706972344914278109) : ℚ) := by
  unfold recurrence2B5A5
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
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_41 :
    recurrence2B5A5.coeff 41 =
      ((1339547 * 10 ^ 70 +
        1092926106489556310071624690227207638056643883750800583928472301093272) : ℚ) := by
  unfold recurrence2B5A5
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
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_42 :
    recurrence2B5A5.coeff 42 =
      -((14246394 * 10 ^ 70 +
        3053152952050798316763955989349426829592179700145229595103682879712145) : ℚ) := by
  unfold recurrence2B5A5
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
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_43 :
    recurrence2B5A5.coeff 43 =
      ((139196139 * 10 ^ 70 +
        5285988047733270917688173204813473721323221884026785803613308715712063) : ℚ) := by
  unfold recurrence2B5A5
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
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_44 :
    recurrence2B5A5.coeff 44 =
      -((1263386635 * 10 ^ 70 +
        2555040234010374836089867126520647086470566961242302791875733412906526) : ℚ) := by
  unfold recurrence2B5A5
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
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_45 :
    recurrence2B5A5.coeff 45 =
      ((10732168877 * 10 ^ 70 +
        5436264412772173729807127907381351282711948457848908825947630986056461) : ℚ) := by
  unfold recurrence2B5A5
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
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_46 :
    recurrence2B5A5.coeff 46 =
      -((85452361286 * 10 ^ 70 +
        4195447832441948004586242082383438596991915759148769708558000489803761) : ℚ) := by
  unfold recurrence2B5A5
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
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_47 :
    recurrence2B5A5.coeff 47 =
      ((636440723477 * 10 ^ 70 +
        1044631631524470586196420583424854092079211737460467700884828514271190) : ℚ) := by
  unfold recurrence2B5A5
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
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_48 :
    recurrence2B5A5.coeff 48 =
      -((4431343930180 * 10 ^ 70 +
        8030270270324116480417042959327092652455862867288479792923416202287831) : ℚ) := by
  unfold recurrence2B5A5
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
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_49 :
    recurrence2B5A5.coeff 49 =
      ((28950711388686 * 10 ^ 70 +
        5680033309382179803867387625304772664036368270461437756256009896758212) : ℚ) := by
  unfold recurrence2B5A5
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
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_50 :
    recurrence2B5A5.coeff 50 =
      -((178580339859835 * 10 ^ 70 +
        4819299078030145019193311201523261867501168176586608783489869762646370) : ℚ) := by
  unfold recurrence2B5A5
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
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_51 :
    recurrence2B5A5.coeff 51 =
      ((1044302986250442 * 10 ^ 70 +
        4114279755193451428663342669678473543194844615774169436029470255861617) : ℚ) := by
  unfold recurrence2B5A5
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
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_52 :
    recurrence2B5A5.coeff 52 =
      -((5781233198228835 * 10 ^ 70 +
        0442178956298599425354975652772218706750778627579089786586226241896617) : ℚ) := by
  unfold recurrence2B5A5
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
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_53 :
    recurrence2B5A5.coeff 53 =
      ((30122657881116622 * 10 ^ 70 +
        5599995611807241397627532635293809852582991889319554707878452208112264) : ℚ) := by
  unfold recurrence2B5A5
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
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_54 :
    recurrence2B5A5.coeff 54 =
      -((146891329198516626 * 10 ^ 70 +
        6215991400987827015438957905490046850955114152529811891934045068210727) : ℚ) := by
  unfold recurrence2B5A5
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
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_55 :
    recurrence2B5A5.coeff 55 =
      ((670385955927150971 * 10 ^ 70 +
        1356641854343164763619512757373060950883893291228024834593410526118459) : ℚ) := by
  unfold recurrence2B5A5
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
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_56 :
    recurrence2B5A5.coeff 56 =
      -((2893383779316657063 * 10 ^ 70 +
        6937062634224901487306754976960304223341147410792646576756885244286293) : ℚ) := by
  unfold recurrence2B5A5
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
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_57 :
    recurrence2B5A5.coeff 57 =
      ((12042839746609859004 * 10 ^ 70 +
        0329452763889807759145936048322697719333640640270700082517088578708309) : ℚ) := by
  unfold recurrence2B5A5
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
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_58 :
    recurrence2B5A5.coeff 58 =
      -((48729548995213541657 * 10 ^ 70 +
        1795860800098839280736728973442954585111547764311705696894059471156722) : ℚ) := by
  unfold recurrence2B5A5
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
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_59 :
    recurrence2B5A5.coeff 59 =
      ((184048556909700639878 * 10 ^ 70 +
        6138817478225033435762842450408436826850499905112320857439592836036164) : ℚ) := by
  unfold recurrence2B5A5
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
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_60 :
    recurrence2B5A5.coeff 60 =
      -((582768276361264140390 * 10 ^ 70 +
        7066976207048479980519682281810024783124421745989044409166018600105232) : ℚ) := by
  unfold recurrence2B5A5
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
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_61 :
    recurrence2B5A5.coeff 61 =
      ((1309307530644466238292 * 10 ^ 70 +
        0290052624677434039733331633076022965987740686228554447555304623870980) : ℚ) := by
  unfold recurrence2B5A5
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
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_62 :
    recurrence2B5A5.coeff 62 =
      -((2012260670167729121649 * 10 ^ 70 +
        2110656780510929024541370794798323972430497495172524819170264631370971) : ℚ) := by
  unfold recurrence2B5A5
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
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_63 :
    recurrence2B5A5.coeff 63 =
      ((10312025452356734163176 * 10 ^ 70 +
        2416344361292935257483304520649466886358614787589956072489457853629611) : ℚ) := by
  unfold recurrence2B5A5
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
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_64 :
    recurrence2B5A5.coeff 64 =
      -((90484595353495780752015 * 10 ^ 70 +
        5661155956101495240462445104302582089657133398969634413835354035838261) : ℚ) := by
  unfold recurrence2B5A5
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
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_65 :
    recurrence2B5A5.coeff 65 =
      ((330703686398681817994904 * 10 ^ 70 +
        0995836542248279888324267394488695406039696388217678442579209533176765) : ℚ) := by
  unfold recurrence2B5A5
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
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_66 :
    recurrence2B5A5.coeff 66 =
      ((549585703060654658135064 * 10 ^ 70 +
        3004451799673560375316139127271050011851761062897678817950961099610432) : ℚ) := by
  unfold recurrence2B5A5
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
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_67 :
    recurrence2B5A5.coeff 67 =
      -((10022114108828658645969014 * 10 ^ 70 +
        2122855265381314736258559756451391508693999587639755972378699736890589) : ℚ) := by
  unfold recurrence2B5A5
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
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_68 :
    recurrence2B5A5.coeff 68 =
      ((32690436232669074248932938 * 10 ^ 70 +
        6423908953302472043829498127974939130793678540896304971196830508172884) : ℚ) := by
  unfold recurrence2B5A5
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
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_69 :
    recurrence2B5A5.coeff 69 =
      ((33484773678803146345776055 * 10 ^ 70 +
        3138255360589762641455205779664875472297567231527419531919150762415278) : ℚ) := by
  unfold recurrence2B5A5
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
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_70 :
    recurrence2B5A5.coeff 70 =
      -((512124242060910882740147025 * 10 ^ 70 +
        4096247085927483700833822087981613745972782171619544163598788601869957) : ℚ) := by
  unfold recurrence2B5A5
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
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_71 :
    recurrence2B5A5.coeff 71 =
      ((883378205697864783360569103 * 10 ^ 70 +
        3315290787004148782718702571287112377779781169256095254491647010431802) : ℚ) := by
  unfold recurrence2B5A5
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
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_72 :
    recurrence2B5A5.coeff 72 =
      ((1854938110861690296029793834 * 10 ^ 70 +
        9358457777517276755116686082207389689556259522118949295827601033013705) : ℚ) := by
  unfold recurrence2B5A5
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
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_73 :
    recurrence2B5A5.coeff 73 =
      ((2404904517652049818747318659 * 10 ^ 70 +
        6385492411485499263321782585228875721251726247182958549857526838925893) : ℚ) := by
  unfold recurrence2B5A5
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
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_74 :
    recurrence2B5A5.coeff 74 =
      -((20813338234613734708403321312 * 10 ^ 70 +
        2778656574527874413641048194776586876608619397999285636971857543995919) : ℚ) := by
  unfold recurrence2B5A5
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
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_75 :
    recurrence2B5A5.coeff 75 =
      -((687943900928278828945898393727 * 10 ^ 70 +
        1413085476667554689035764697290035962427084528579810316307654801010129) : ℚ) := by
  unfold recurrence2B5A5
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
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_76 :
    recurrence2B5A5.coeff 76 =
      ((5438466589811649217440221110876 * 10 ^ 70 +
        3301634799213953554761926274925696512820855673980664537556665914568104) : ℚ) := by
  unfold recurrence2B5A5
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
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_77 :
    recurrence2B5A5.coeff 77 =
      -((4888661427271195343429335547994 * 10 ^ 70 +
        2751424688639078226790651470708738959249026108761306736838266819864764) : ℚ) := by
  unfold recurrence2B5A5
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
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_78 :
    recurrence2B5A5.coeff 78 =
      -((125765047240486500365698327816461 * 10 ^ 70 +
        6392368624055119569980110128844673456077779558202299749679085287821877) : ℚ) := by
  unfold recurrence2B5A5
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
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_79 :
    recurrence2B5A5.coeff 79 =
      ((660241298695173323706040910023909 * 10 ^ 70 +
        6200547603278575983348994583584452228927130026872050575255707835299364) : ℚ) := by
  unfold recurrence2B5A5
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
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_80 :
    recurrence2B5A5.coeff 80 =
      -((45115928433582491090350496767041 * 10 ^ 70 +
        9009399298158183141570472313050523204201884558645349490151029164935491) : ℚ) := by
  unfold recurrence2B5A5
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
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_81 :
    recurrence2B5A5.coeff 81 =
      -((12502117024948274438277835064561688 * 10 ^ 70 +
        2268670007625222028306432525293763953236223755399704485416546337025757) : ℚ) := by
  unfold recurrence2B5A5
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
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_82 :
    recurrence2B5A5.coeff 82 =
      ((46924743289043251861852685840785785 * 10 ^ 70 +
        6701118631387370194329843298688979983397331849960720983754004737998668) : ℚ) := by
  unfold recurrence2B5A5
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
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_83 :
    recurrence2B5A5.coeff 83 =
      ((41455641286725217259936234640223761 * 10 ^ 70 +
        7099086735305615737784926861097085148590847595018905755294177850072633) : ℚ) := by
  unfold recurrence2B5A5
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
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_84 :
    recurrence2B5A5.coeff 84 =
      -((866540666595846629922104917744723840 * 10 ^ 70 +
        0785423321899303801146570557115342690339088942054904630410018911584788) : ℚ) := by
  unfold recurrence2B5A5
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
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_85 :
    recurrence2B5A5.coeff 85 =
      ((2138153772143649385560125475149517665 * 10 ^ 70 +
        9547051158250049987923832423971618706576047399208792566282241686634292) : ℚ) := by
  unfold recurrence2B5A5
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
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_86 :
    recurrence2B5A5.coeff 86 =
      ((5873633165026873320984332379100395519 * 10 ^ 70 +
        1939060995260928732160952186450195834360703778548740857974455261501417) : ℚ) := by
  unfold recurrence2B5A5
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
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_87 :
    recurrence2B5A5.coeff 87 =
      -((46962457350173792837783388456976017482 * 10 ^ 70 +
        2230935996789099129344954541955012944034506815704037249791424395675932) : ℚ) := by
  unfold recurrence2B5A5
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
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_88 :
    recurrence2B5A5.coeff 88 =
      ((52317925878723617353115150557676447707 * 10 ^ 70 +
        7121081987088475166107870507704542227397763596610735816581217601441130) : ℚ) := by
  unfold recurrence2B5A5
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
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_89 :
    recurrence2B5A5.coeff 89 =
      ((505306753465437557167184303071616218039 * 10 ^ 70 +
        6708811380225452158689542040566149278739611815019211592841036641868396) : ℚ) := by
  unfold recurrence2B5A5
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
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_90 :
    recurrence2B5A5.coeff 90 =
      -((2202261449535010434163968064449512162791 * 10 ^ 70 +
        8050786445327090195412725429132338058495504298172541498474542320581127) : ℚ) := by
  unfold recurrence2B5A5
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
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_91 :
    recurrence2B5A5.coeff 91 =
      -((461761154426498668205086701151368638942 * 10 ^ 70 +
        3550063674492397096921471902040393393825911153233560099114588862165407) : ℚ) := by
  unfold recurrence2B5A5
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
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_92 :
    recurrence2B5A5.coeff 92 =
      ((31977416377101920048553167418484054667234 * 10 ^ 70 +
        1466874661113294784338129347080566789163474448047527346143022194828129) : ℚ) := by
  unfold recurrence2B5A5
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
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_93 :
    recurrence2B5A5.coeff 93 =
      -((96447869995230567912752327918653666844960 * 10 ^ 70 +
        5479302688685278985268922566509540457002064494171118781668820452828246) : ℚ) := by
  unfold recurrence2B5A5
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
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_94 :
    recurrence2B5A5.coeff 94 =
      -((104536145826807997807115943201096874419200 * 10 ^ 70 +
        7848871698979431205044655061953139355622671362859335895245996234073843) : ℚ) := by
  unfold recurrence2B5A5
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
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_95 :
    recurrence2B5A5.coeff 95 =
      ((1573367650147263580072359311233355797767655 * 10 ^ 70 +
        5875106249716526937211656132287572551824236694866008961751718160516135) : ℚ) := by
  unfold recurrence2B5A5
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
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_96 :
    recurrence2B5A5.coeff 96 =
      -((3978443746927996523155262065257612940926229 * 10 ^ 70 +
        2226438312754317374870459170902411965518168008034768374021271186828480) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 97 = 0 +
    97 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 97 = 32 +
      65 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 65 = 32 +
      33 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 33 = 32 +
      1 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 1 = 1 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_97 :
    recurrence2B5A5.coeff 97 =
      -((5264601326761235880905001385479440741621568 * 10 ^ 70 +
        8741731558492990534823729378944158075787305281519145572126108240095001) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 98 = 0 +
    98 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 98 = 32 +
      66 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 66 = 32 +
      34 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 34 = 32 +
      2 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 2 = 2 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence2B5A5_coeff_98 :
    recurrence2B5A5.coeff 98 =
      ((62989457922188747333126280852545001330565412 * 10 ^ 70 +
        5589478656417350081603199121058788287627559850711523059102042210272309) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 99 = 0 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_99_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (99 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (99 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A5_coeff_99 :
    recurrence2B5A5.coeff 99 =
      -((152228129947026790140370756113630363811684514 * 10 ^ 70 +
        9409784843572759198823639447850326886588256684088245442609492448831601) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 100 = 1 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_99_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_100_prefix_zero :
    (∑ x ∈ Finset.range 2,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (100 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (100 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A5_coeff_100 :
    recurrence2B5A5.coeff 100 =
      -((167385292790887862063061754843699209562100112 * 10 ^ 70 +
        1925407670018496626679792952406454805806670293390431640193126084880930) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 101 = 2 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_100_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_101_prefix_zero :
    (∑ x ∈ Finset.range 3,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (101 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (101 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A5_coeff_101 :
    recurrence2B5A5.coeff 101 =
      ((2147880835150847994138379480283643842377642321 * 10 ^ 70 +
        2062115809981214299375469930401018361567371679417953754059415418839319) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 102 = 3 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_101_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_102_prefix_zero :
    (∑ x ∈ Finset.range 4,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (102 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (102 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A5_coeff_102 :
    recurrence2B5A5.coeff 102 =
      -((5494623877420088579254490888705822446615587084 * 10 ^ 70 +
        3939401275783115394678823457277113562176583584522885960758332095352338) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 103 = 4 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_102_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_103_prefix_zero :
    (∑ x ∈ Finset.range 5,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (103 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (103 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A5_coeff_103 :
    recurrence2B5A5.coeff 103 =
      -((2801353061546769508040666130786487613559974421 * 10 ^ 70 +
        9923184386866642813990986158786999004407088936967392943419025219695920) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 104 = 5 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_103_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_104_prefix_zero :
    (∑ x ∈ Finset.range 6,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (104 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (104 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A5_coeff_104 :
    recurrence2B5A5.coeff 104 =
      ((62499730823457233507900941407091275293484920376 * 10 ^ 70 +
        1727125655462618325538866478494968248935789398079899691357656197035931) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 105 = 6 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_104_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_105_prefix_zero :
    (∑ x ∈ Finset.range 7,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (105 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (105 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A5_coeff_105 :
    recurrence2B5A5.coeff 105 =
      -((185664109930140299481737969322693150079597930461 * 10 ^ 70 +
        3840098003079233313689281463710099957714429303989458834896474137267277) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 106 = 7 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_105_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_106_prefix_zero :
    (∑ x ∈ Finset.range 8,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (106 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (106 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A5_coeff_106 :
    recurrence2B5A5.coeff 106 =
      ((60508186038433147621410291390990134861162280578 * 10 ^ 70 +
        0863032141810914184822328317293239212025092446288221446018263700737783) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 107 = 8 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_106_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_107_prefix_zero :
    (∑ x ∈ Finset.range 9,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (107 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (107 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A5_coeff_107 :
    recurrence2B5A5.coeff 107 =
      ((1445727324665536949873882282826177199838408247820 * 10 ^ 70 +
        7628970148506408252741329581817568959793303553863795013173938828818266) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 108 = 9 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_107_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_108_prefix_zero :
    (∑ x ∈ Finset.range 10,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (108 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (108 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A5_coeff_108 :
    recurrence2B5A5.coeff 108 =
      -((5481939719986811448183527340715528045462701330210 * 10 ^ 70 +
        9783885511987216987784455360028171946401453447496016417532427095981202) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 109 = 10 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_108_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_109_prefix_zero :
    (∑ x ∈ Finset.range 11,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (109 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (109 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A5_coeff_109 :
    recurrence2B5A5.coeff 109 =
      ((6687225982244327002398160479049647100492319993276 * 10 ^ 70 +
        5937810928379501291911785819542961180845081552357488533766297513632788) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 110 = 11 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_109_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_110_prefix_zero :
    (∑ x ∈ Finset.range 12,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (110 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (110 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A5_coeff_110 :
    recurrence2B5A5.coeff 110 =
      ((21794803711445893346563223230020283549030975949111 * 10 ^ 70 +
        0877787239281559223256629802933180234469328146693309946596410503422259) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 111 = 12 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_110_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_111_prefix_zero :
    (∑ x ∈ Finset.range 13,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (111 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (111 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A5_coeff_111 :
    recurrence2B5A5.coeff 111 =
      -((128537344573823515860825814251850354224141030072861 * 10 ^ 70 +
        7876550105842506896890008298090389000020598716099483663952806671610876) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 112 = 13 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_111_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_112_prefix_zero :
    (∑ x ∈ Finset.range 14,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (112 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (112 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A5_coeff_112 :
    recurrence2B5A5.coeff 112 =
      ((276837282412874354510705825164982584688005824422654 * 10 ^ 70 +
        3458767499549862256203739577285214388591443266564841083188681200908344) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 113 = 14 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_112_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_113_prefix_zero :
    (∑ x ∈ Finset.range 15,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (113 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (113 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A5_coeff_113 :
    recurrence2B5A5.coeff 113 =
      ((4770891539897432467085724213580522303332124043765 * 10 ^ 70 +
        8218869599257814988002382007729871999793274181762954484147365952553719) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 114 = 15 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_113_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_114_prefix_zero :
    (∑ x ∈ Finset.range 16,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (114 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (114 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A5_coeff_114 :
    recurrence2B5A5.coeff 114 =
      -((2038606843272342957459658742486931504774367335739939 * 10 ^ 70 +
        0085643792930920817696253890034231180175970019430854061459312333210800) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 115 = 16 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_114_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_115_prefix_zero :
    (∑ x ∈ Finset.range 17,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (115 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (115 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A5_coeff_115 :
    recurrence2B5A5.coeff 115 =
      ((7072816584894773207436366422914758822316623817193885 * 10 ^ 70 +
        4845576826934958536552024126912392823555755062141441568641243337672163) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 116 = 17 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_115_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_116_prefix_zero :
    (∑ x ∈ Finset.range 18,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (116 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (116 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A5_coeff_116 :
    recurrence2B5A5.coeff 116 =
      -((10646016789721008740126969176069633355435941363945135 * 10 ^ 70 +
        9970153177010394351738165237071854504554468090784480344397613245357742) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 117 = 18 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_116_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_117_prefix_zero :
    (∑ x ∈ Finset.range 19,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (117 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (117 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A5_coeff_117 :
    recurrence2B5A5.coeff 117 =
      -((10108359735580271902693303608865030715766867692965368 * 10 ^ 70 +
        7800600033877894920143335160252089391195230049206228892756430980988133) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 118 = 19 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_117_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_118_prefix_zero :
    (∑ x ∈ Finset.range 20,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (118 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (118 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A5_coeff_118 :
    recurrence2B5A5.coeff 118 =
      ((104558870520466199999349956567332148883338672861741214 * 10 ^ 70 +
        3422160554715493986635444494810162344541154760632396861812600036353204) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 119 = 20 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_118_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_119_prefix_zero :
    (∑ x ∈ Finset.range 21,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (119 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (119 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A5_coeff_119 :
    recurrence2B5A5.coeff 119 =
      -((302760837749119624545599295230916723940787847864252537 * 10 ^ 70 +
        5029867686598705207108784860975601426537439056351304069121434247107358) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 120 = 21 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_119_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_120_prefix_zero :
    (∑ x ∈ Finset.range 22,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (120 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (120 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A5_coeff_120 :
    recurrence2B5A5.coeff 120 =
      ((422711544389109955843481518906490209782011011007617654 * 10 ^ 70 +
        7177885256375121961127605782575343987645211138140050784569780674358589) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 121 = 22 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_120_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_121_prefix_zero :
    (∑ x ∈ Finset.range 23,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (121 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (121 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A5_coeff_121 :
    recurrence2B5A5.coeff 121 =
      ((311072965803794884295475636191815247996894655559599821 * 10 ^ 70 +
        1734830201499623783027877453566366629023491325880823021749158532362261) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 122 = 23 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_121_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_122_prefix_zero :
    (∑ x ∈ Finset.range 24,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (122 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (122 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A5_coeff_122 :
    recurrence2B5A5.coeff 122 =
      -((3519628598872765483350283717370279944458250313964182449 * 10 ^ 70 +
        8113255697444396306285086676110537442409339778621911282583924669543218) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 123 = 24 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_122_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_123_prefix_zero :
    (∑ x ∈ Finset.range 25,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (123 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (123 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A5_coeff_123 :
    recurrence2B5A5.coeff 123 =
      ((10623324124165816284703180362101213337050524676813918091 * 10 ^ 70 +
        6627316297838418642179180419833000872063585591057492848750490211836131) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 124 = 25 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_123_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_124_prefix_zero :
    (∑ x ∈ Finset.range 26,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (124 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (124 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A5_coeff_124 :
    recurrence2B5A5.coeff 124 =
      -((18328563121949487226499513564651028257121794973838847931 * 10 ^ 70 +
        5466871637884385839871533911121853397176884323627195829705439442924311) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 125 = 26 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_124_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_125_prefix_zero :
    (∑ x ∈ Finset.range 27,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (125 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (125 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A5_coeff_125 :
    recurrence2B5A5.coeff 125 =
      ((8974023919204165749981836646197752100987002854760177542 * 10 ^ 70 +
        1628636570281124820909059170639802099705087000590990438905536401751006) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 126 = 27 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_125_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_126_prefix_zero :
    (∑ x ∈ Finset.range 28,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (126 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (126 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A5_coeff_126 :
    recurrence2B5A5.coeff 126 =
      ((60683729946416425780309892514589004647925259401433751380 * 10 ^ 70 +
        5508015119499546491666693605071329431554148858341564766624912113181853) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 127 = 28 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_126_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_127_prefix_zero :
    (∑ x ∈ Finset.range 29,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (127 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (127 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A5_coeff_127 :
    recurrence2B5A5.coeff 127 =
      -((255463691729121037171467580481664923191220300740160345429 * 10 ^ 70 +
        8912026291644702718672268750677147205334386709236312203524706047853337) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 128 = 29 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_127_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_128_prefix_zero :
    (∑ x ∈ Finset.range 30,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (128 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (128 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A5_coeff_128 :
    recurrence2B5A5.coeff 128 =
      ((606543572243393734516848957764589121412451695785022833156 * 10 ^ 70 +
        5216454072650744028386446925042474656423109813096384193560353788425947) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 129 = 30 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_128_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_129_prefix_zero :
    (∑ x ∈ Finset.range 31,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (129 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (129 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A5_coeff_129 :
    recurrence2B5A5.coeff 129 =
      -((958080272522351172082499586571422721004102243087948916880 * 10 ^ 70 +
        8267876043187310442613185851935396747337831524527773126438978411918375) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 130 = 31 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_129_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_130_prefix_zero :
    (∑ x ∈ Finset.range 32,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (130 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (130 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A5_coeff_130 :
    recurrence2B5A5.coeff 130 =
      ((695460399621480617323118227775029884243600426597402953206 * 10 ^ 70 +
        8844305715294285056403859508768311465250399334811905801998954263467692) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 131 = 32 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_130_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_131_prefix_zero :
    (∑ x ∈ Finset.range 33,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (131 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (131 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A5_coeff_131 :
    recurrence2B5A5.coeff 131 =
      ((1567723951587548541126846367561155916849247497683525453454 * 10 ^ 70 +
        3789127839273236469896181634619903491805349424075355127796731355753372) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 132 = 33 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_131_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_132_prefix_zero :
    (∑ x ∈ Finset.range 34,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (132 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (132 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A5_coeff_132 :
    recurrence2B5A5.coeff 132 =
      -((8095755884502474779751919957718115026885445541543122544641 * 10 ^ 70 +
        5439009586030065241778849176783853636619129307475619891913450454427990) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 133 = 34 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_132_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_133_prefix_zero :
    (∑ x ∈ Finset.range 35,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (133 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (133 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A5_coeff_133 :
    recurrence2B5A5.coeff 133 =
      ((21506149044147142678809135588045111768168932129891561462563 * 10 ^ 70 +
        0863877428974956356731889876137628452617681324006866810005534567509138) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 134 = 35 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_133_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_134_prefix_zero :
    (∑ x ∈ Finset.range 36,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (134 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (134 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2B5A5_coeff_134 :
    recurrence2B5A5.coeff 134 =
      -((43169513167468719310788489823976920270010713952248570518133 * 10 ^ 70 +
        9343579772159136809484366537688460687145375816403846441234336994322297) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 135 = 36 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_134_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_135_prefix_zero :
    (∑ x ∈ Finset.range 37,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (135 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (135 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_135_suffix_zero :
    (∑ x ∈ Finset.range 1,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (135 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_135 :
    recurrence2B5A5.coeff 135 =
      ((70415394103525877200388196607983448066179082707676636449786 * 10 ^ 70 +
        6144582242908691097029425612320193704925262315670847057579500941072156) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 136 = 37 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_135_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_135_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_136_prefix_zero :
    (∑ x ∈ Finset.range 38,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (136 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (136 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_136_suffix_zero :
    (∑ x ∈ Finset.range 2,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (136 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_136 :
    recurrence2B5A5.coeff 136 =
      -((93179888933750955339721850079709797102476490030382719515507 * 10 ^ 70 +
        2224239374254746011220806635571772692296182661609783346523779906096891) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 137 = 38 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 1 +
      2 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_136_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_136_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_137_prefix_zero :
    (∑ x ∈ Finset.range 39,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (137 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (137 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_137_suffix_zero :
    (∑ x ∈ Finset.range 3,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (137 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_137 :
    recurrence2B5A5.coeff 137 =
      ((91708479312566736806648423253530303653846102804724696569386 * 10 ^ 70 +
        7863612600510908025617508866701962682074927808359336440997550814474155) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 138 = 39 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_137_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_137_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_138_prefix_zero :
    (∑ x ∈ Finset.range 40,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (138 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (138 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_138_suffix_zero :
    (∑ x ∈ Finset.range 4,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (138 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_138 :
    recurrence2B5A5.coeff 138 =
      -((37576001951732482216207535846932954448275181651083757898263 * 10 ^ 70 +
        7441704380845435819407581335636633145515579653954021949306856294983046) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 139 = 40 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 31 +
      4 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_138_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_138_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_139_prefix_zero :
    (∑ x ∈ Finset.range 41,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (139 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (139 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_139_suffix_zero :
    (∑ x ∈ Finset.range 5,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (139 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_139 :
    recurrence2B5A5.coeff 139 =
      -((100103156609474544090869673445340371890641276998680194648197 * 10 ^ 70 +
        5629763975888291549500234251138204994651269069606711562273540636662257) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 140 = 41 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 30 +
      5 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_139_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_139_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_140_prefix_zero :
    (∑ x ∈ Finset.range 42,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (140 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (140 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_140_suffix_zero :
    (∑ x ∈ Finset.range 6,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (140 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_140 :
    recurrence2B5A5.coeff 140 =
      ((343239093126850199409266810923880763812956127035691909230815 * 10 ^ 70 +
        7588071527522148754190743858863786417317427862705583765342042333879395) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 141 = 42 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 29 +
      6 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_140_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_140_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_141_prefix_zero :
    (∑ x ∈ Finset.range 43,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (141 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (141 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_141_suffix_zero :
    (∑ x ∈ Finset.range 7,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (141 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_141 :
    recurrence2B5A5.coeff 141 =
      -((690980098621763725340786814082182642068815880733572108827186 * 10 ^ 70 +
        7075212575917088856337679401744734938389912233274947238716711140748755) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 142 = 43 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 28 +
      7 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_141_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_141_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_142_prefix_zero :
    (∑ x ∈ Finset.range 44,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (142 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (142 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_142_suffix_zero :
    (∑ x ∈ Finset.range 8,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (142 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_142 :
    recurrence2B5A5.coeff 142 =
      ((1109129407487677851175861106516722343951030740824667791701334 * 10 ^ 70 +
        7352227265382854579038445938443184327271255507397204734267923468599643) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 143 = 44 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 27 +
      8 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_142_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_142_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_143_prefix_zero :
    (∑ x ∈ Finset.range 45,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (143 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (143 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_143_suffix_zero :
    (∑ x ∈ Finset.range 9,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (143 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_143 :
    recurrence2B5A5.coeff 143 =
      -((1529013062289423212879401365969267128192659865689374493890043 * 10 ^ 70 +
        4362360699391505494387685600480645577207225247359634370384579539975817) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 144 = 45 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 26 +
      9 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_143_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_143_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_144_prefix_zero :
    (∑ x ∈ Finset.range 46,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (144 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (144 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_144_suffix_zero :
    (∑ x ∈ Finset.range 10,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (144 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_144 :
    recurrence2B5A5.coeff 144 =
      ((1859584225053634310869286211417725448481432170020717162132843 * 10 ^ 70 +
        7814181273419172063942596781036779429943702408729129609763134622044370) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 145 = 46 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 25 +
      10 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_144_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_144_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_145_prefix_zero :
    (∑ x ∈ Finset.range 47,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (145 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (145 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_145_suffix_zero :
    (∑ x ∈ Finset.range 11,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (145 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_145 :
    recurrence2B5A5.coeff 145 =
      -((2011317215075961494351340962022835915923937671187966192434168 * 10 ^ 70 +
        4420060624743909468507100661374392437232588925919444920828476296645899) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 146 = 47 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 24 +
      11 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_145_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_145_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_146_prefix_zero :
    (∑ x ∈ Finset.range 48,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (146 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (146 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_146_suffix_zero :
    (∑ x ∈ Finset.range 12,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (146 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_146 :
    recurrence2B5A5.coeff 146 =
      ((1924612952831771395070233917109735001585396706886867624217480 * 10 ^ 70 +
        3493226954118467439807332128749333266789099768831077075478782535535533) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 147 = 48 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 23 +
      12 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_146_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_146_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_147_prefix_zero :
    (∑ x ∈ Finset.range 49,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (147 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (147 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_147_suffix_zero :
    (∑ x ∈ Finset.range 13,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (147 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_147 :
    recurrence2B5A5.coeff 147 =
      -((1592036901296927825444330876397693050583979339325035682681958 * 10 ^ 70 +
        5518284332240674905529927540457694385803472480271200829789023732179868) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 148 = 49 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 22 +
      13 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_147_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_147_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_148_prefix_zero :
    (∑ x ∈ Finset.range 50,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (148 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (148 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_148_suffix_zero :
    (∑ x ∈ Finset.range 14,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (148 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_148 :
    recurrence2B5A5.coeff 148 =
      ((1064946972295092797812317873723683816227612700681325549666359 * 10 ^ 70 +
        9997639275351658009663599065551326074293901361762891711920430058497377) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 149 = 50 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 21 +
      14 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_148_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_148_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_149_prefix_zero :
    (∑ x ∈ Finset.range 51,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (149 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (149 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_149_suffix_zero :
    (∑ x ∈ Finset.range 15,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (149 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_149 :
    recurrence2B5A5.coeff 149 =
      -((440875901971212736872812383350688882379819217417589778707022 * 10 ^ 70 +
        5915433452113749523599927524086640465178442361821377864985805613692931) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 150 = 51 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 20 +
      15 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_149_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_149_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_150_prefix_zero :
    (∑ x ∈ Finset.range 52,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (150 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (150 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_150_suffix_zero :
    (∑ x ∈ Finset.range 16,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (150 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_150 :
    recurrence2B5A5.coeff 150 =
      -((164142422274706658835691488914614542392034628405314118141418 * 10 ^ 70 +
        2401434226499981749700275178698778191994387492673927115843743800818346) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 151 = 52 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 19 +
      16 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_150_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_150_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_151_prefix_zero :
    (∑ x ∈ Finset.range 53,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (151 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (151 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_151_suffix_zero :
    (∑ x ∈ Finset.range 17,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (151 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_151 :
    recurrence2B5A5.coeff 151 =
      ((648025153437456784317220019643038658119138516933896880022418 * 10 ^ 70 +
        4845033193928136148085770992094126998386637407472999842601064934057920) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 152 = 53 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 18 +
      17 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_151_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_151_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_152_prefix_zero :
    (∑ x ∈ Finset.range 54,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (152 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (152 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_152_suffix_zero :
    (∑ x ∈ Finset.range 18,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (152 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_152 :
    recurrence2B5A5.coeff 152 =
      -((948140119629534616840808969400682473330237126023123945034358 * 10 ^ 70 +
        0213382402575974839554201509837396658565336563635920543042439513299269) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 153 = 54 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 17 +
      18 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_152_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_152_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_153_prefix_zero :
    (∑ x ∈ Finset.range 55,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (153 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (153 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_153_suffix_zero :
    (∑ x ∈ Finset.range 19,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (153 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_153 :
    recurrence2B5A5.coeff 153 =
      ((1051771277483126411177091412017410904613197809049076821790900 * 10 ^ 70 +
        7054392722756323597129145797250854069360094858937811957607139166771314) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 154 = 55 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 16 +
      19 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_153_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_153_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_154_prefix_zero :
    (∑ x ∈ Finset.range 56,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (154 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (154 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_154_suffix_zero :
    (∑ x ∈ Finset.range 20,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (154 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_154 :
    recurrence2B5A5.coeff 154 =
      -((990126751197832012635280173916724501654442171502752436207128 * 10 ^ 70 +
        9529498338587504886993620821564429075128729739747832589072009157884006) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 155 = 56 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 15 +
      20 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_154_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_154_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_155_prefix_zero :
    (∑ x ∈ Finset.range 57,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (155 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (155 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_155_suffix_zero :
    (∑ x ∈ Finset.range 21,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (155 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_155 :
    recurrence2B5A5.coeff 155 =
      ((820789252702054112683085934788606507696256372999186696660648 * 10 ^ 70 +
        0903674665838052990301917064622792982519158332931540479017459039305036) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 156 = 57 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 14 +
      21 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_155_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_155_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_156_prefix_zero :
    (∑ x ∈ Finset.range 58,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (156 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (156 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_156_suffix_zero :
    (∑ x ∈ Finset.range 22,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (156 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_156 :
    recurrence2B5A5.coeff 156 =
      -((606768236744900267375177945674278031122884002698666810331845 * 10 ^ 70 +
        2947850488367330966872007893855147851772227798200302362802823779666109) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 157 = 58 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 13 +
      22 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_156_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_156_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_157_prefix_zero :
    (∑ x ∈ Finset.range 59,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (157 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (157 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_157_suffix_zero :
    (∑ x ∈ Finset.range 23,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (157 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_157 :
    recurrence2B5A5.coeff 157 =
      ((399678817821254759883412578517026377162076081214038789710220 * 10 ^ 70 +
        1681277082460903087875720420784371451197422159665882873558968826993879) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 158 = 59 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 12 +
      23 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_157_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_157_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_158_prefix_zero :
    (∑ x ∈ Finset.range 60,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (158 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (158 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_158_suffix_zero :
    (∑ x ∈ Finset.range 24,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (158 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_158 :
    recurrence2B5A5.coeff 158 =
      -((231172205416096983983285409492526635887787507607781219828473 * 10 ^ 70 +
        3262393966256186893259204421500724798085300687262005907468297637539918) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 159 = 60 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 11 +
      24 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_158_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_158_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_159_prefix_zero :
    (∑ x ∈ Finset.range 61,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (159 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (159 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_159_suffix_zero :
    (∑ x ∈ Finset.range 25,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (159 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_159 :
    recurrence2B5A5.coeff 159 =
      ((112690599799975751598621819620240003099731877147266982929069 * 10 ^ 70 +
        6002473408124197868911900916884366487607199122722530150655794127778391) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 160 = 61 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 10 +
      25 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_159_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_159_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_160_prefix_zero :
    (∑ x ∈ Finset.range 62,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (160 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (160 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_160_suffix_zero :
    (∑ x ∈ Finset.range 26,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (160 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_160 :
    recurrence2B5A5.coeff 160 =
      -((40762053434369645662935395757595682993534955501519515882292 * 10 ^ 70 +
        2262708445303468574718085798865813070387218944492936178222162293984502) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 161 = 62 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 9 +
      26 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_160_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_160_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_161_prefix_zero :
    (∑ x ∈ Finset.range 63,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (161 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (161 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_161_suffix_zero :
    (∑ x ∈ Finset.range 27,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (161 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_161 :
    recurrence2B5A5.coeff 161 =
      ((4169589151242372274043552027739937198512238908318314990761 * 10 ^ 70 +
        1214460083711533136920009121189549440176452395660858354811275096657392) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 162 = 63 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 8 +
      27 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_161_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_161_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_162_prefix_zero :
    (∑ x ∈ Finset.range 64,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (162 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (162 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_162_suffix_zero :
    (∑ x ∈ Finset.range 28,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (162 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_162 :
    recurrence2B5A5.coeff 162 =
      ((9897756572368838469914250770415119348386004520657265924878 * 10 ^ 70 +
        5761730848523856757391783355161271507250147496168613644298420998034077) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 163 = 64 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 7 +
      28 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_162_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_162_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_163_prefix_zero :
    (∑ x ∈ Finset.range 65,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (163 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (163 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_163_suffix_zero :
    (∑ x ∈ Finset.range 29,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (163 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_163 :
    recurrence2B5A5.coeff 163 =
      -((12088798687349315439660253301780397506666120717294490090796 * 10 ^ 70 +
        2625993756775314513017133634675764881719323770284781868750374386269628) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 164 = 65 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 6 +
      29 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_163_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_163_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_164_prefix_zero :
    (∑ x ∈ Finset.range 66,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (164 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (164 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_164_suffix_zero :
    (∑ x ∈ Finset.range 30,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (164 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_164 :
    recurrence2B5A5.coeff 164 =
      ((9528674209605353324366951819035388156853996771399484937925 * 10 ^ 70 +
        5576351158608024104444087375641974042092076006829152398342526096658923) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 165 = 66 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 5 +
      30 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_164_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_164_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_165_prefix_zero :
    (∑ x ∈ Finset.range 67,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (165 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (165 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_165_suffix_zero :
    (∑ x ∈ Finset.range 31,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (165 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_165 :
    recurrence2B5A5.coeff 165 =
      -((6082045909492992782126766409548919988818228660750720656960 * 10 ^ 70 +
        4212701664400434130440457219567624739517234671123193014538160077205791) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 166 = 67 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 4 +
      31 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_165_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_165_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_166_prefix_zero :
    (∑ x ∈ Finset.range 68,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (166 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (166 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_166_suffix_zero :
    (∑ x ∈ Finset.range 32,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (166 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_166 :
    recurrence2B5A5.coeff 166 =
      ((3329378534968224915952869711204042863718687213561003482639 * 10 ^ 70 +
        3361667133399304978824122091907973077499131112149362484073415742092298) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 167 = 68 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 3 +
      32 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_166_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_166_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_167_prefix_zero :
    (∑ x ∈ Finset.range 69,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (167 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (167 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_167_suffix_zero :
    (∑ x ∈ Finset.range 33,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (167 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_167 :
    recurrence2B5A5.coeff 167 =
      -((1587859632975653034360677559561395179957681717274778495435 * 10 ^ 70 +
        7843415477681565644046905817079382179235044997196316866583662261623401) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 168 = 69 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 2 +
      33 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_167_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_167_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_168_prefix_zero :
    (∑ x ∈ Finset.range 70,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (168 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (168 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_168_suffix_zero :
    (∑ x ∈ Finset.range 34,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (168 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_168 :
    recurrence2B5A5.coeff 168 =
      ((655564405273264130450923549481434063714824424671240023170 * 10 ^ 70 +
        0458318199050918503101132272618939666094288559433818312678068203960556) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 169 = 70 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 1 +
      34 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_168_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_168_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_169_prefix_zero :
    (∑ x ∈ Finset.range 71,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (169 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (169 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_169_suffix_zero :
    (∑ x ∈ Finset.range 35,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (169 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_169 :
    recurrence2B5A5.coeff 169 =
      -((226453472558118999596474230769943760253357500799161312021 * 10 ^ 70 +
        8498511231353842853149339635192487010012748920676356704910528631076818) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 170 = 71 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_169_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_169_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_170_prefix_zero :
    (∑ x ∈ Finset.range 72,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (170 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (170 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_170_suffix_zero :
    (∑ x ∈ Finset.range 36,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (170 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_170 :
    recurrence2B5A5.coeff 170 =
      ((58625648371274781941207455395395452388756711289418046206 * 10 ^ 70 +
        8299273689226009319288265519648688185476031583395416092279112245504262) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 171 = 72 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 31 +
      36 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_170_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_170_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_171_prefix_zero :
    (∑ x ∈ Finset.range 73,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (171 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (171 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_171_suffix_zero :
    (∑ x ∈ Finset.range 37,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (171 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_171 :
    recurrence2B5A5.coeff 171 =
      -((5729302416722074527709154148625568130681095607061605708 * 10 ^ 70 +
        9839840570744790587129317371418956001113676798093791912165952712859775) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 172 = 73 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 30 +
      37 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_171_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_171_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_172_prefix_zero :
    (∑ x ∈ Finset.range 74,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (172 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (172 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_172_suffix_zero :
    (∑ x ∈ Finset.range 38,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (172 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_172 :
    recurrence2B5A5.coeff 172 =
      -((5235709782651674518679389748590043289673434581577840857 * 10 ^ 70 +
        1044486175220024663411764204745893348311960062087925166630613535587677) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 173 = 74 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 29 +
      38 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_172_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_172_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_173_prefix_zero :
    (∑ x ∈ Finset.range 75,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (173 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (173 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_173_suffix_zero :
    (∑ x ∈ Finset.range 39,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (173 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_173 :
    recurrence2B5A5.coeff 173 =
      ((4582200271156396903317117203645928456427735769176338349 * 10 ^ 70 +
        0297841837557299410649287065427855275372310677639479332382848940996008) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 174 = 75 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 28 +
      39 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_173_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_173_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_174_prefix_zero :
    (∑ x ∈ Finset.range 76,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (174 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (174 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_174_suffix_zero :
    (∑ x ∈ Finset.range 40,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (174 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_174 :
    recurrence2B5A5.coeff 174 =
      -((2401952298446584753933229781291467602678622571345139624 * 10 ^ 70 +
        6787808783090641289239667232474408020945126073040171613828484563000805) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 175 = 76 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 27 +
      40 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_174_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_174_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_175_prefix_zero :
    (∑ x ∈ Finset.range 77,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (175 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (175 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_175_suffix_zero :
    (∑ x ∈ Finset.range 41,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (175 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_175 :
    recurrence2B5A5.coeff 175 =
      ((985677411404353201323607245531612942629421681952456202 * 10 ^ 70 +
        5410970966409471767394859367753867007001897136806545743296708787864847) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 176 = 77 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 26 +
      41 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_175_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_175_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_176_prefix_zero :
    (∑ x ∈ Finset.range 78,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (176 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (176 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_176_suffix_zero :
    (∑ x ∈ Finset.range 42,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (176 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_176 :
    recurrence2B5A5.coeff 176 =
      -((334824481514258366563219740130861114538906204865806677 * 10 ^ 70 +
        4212848644678838646833810974928428648823786701030019038321164697617890) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 177 = 78 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 25 +
      42 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_176_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_176_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_177_prefix_zero :
    (∑ x ∈ Finset.range 79,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (177 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (177 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_177_suffix_zero :
    (∑ x ∈ Finset.range 43,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (177 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_177 :
    recurrence2B5A5.coeff 177 =
      ((94106235894983541712245006949983373082038216711349221 * 10 ^ 70 +
        6887943518285479863013700581042627752108373741343891643790674682993077) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 178 = 79 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 24 +
      43 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_177_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_177_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_178_prefix_zero :
    (∑ x ∈ Finset.range 80,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (178 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (178 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_178_suffix_zero :
    (∑ x ∈ Finset.range 44,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (178 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_178 :
    recurrence2B5A5.coeff 178 =
      -((20739032414285275493481513634443919575650549122153821 * 10 ^ 70 +
        9916168928929790921184366575384303173411596543970995166581434316944164) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 179 = 80 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 23 +
      44 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_178_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_178_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_179_prefix_zero :
    (∑ x ∈ Finset.range 81,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (179 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (179 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_179_suffix_zero :
    (∑ x ∈ Finset.range 45,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (179 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_179 :
    recurrence2B5A5.coeff 179 =
      ((2834060067307601147533497066315176222810608011959334 * 10 ^ 70 +
        1055627289802933936189503961855741924064847577482571382916402172535441) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 180 = 81 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 22 +
      45 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_179_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_179_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_180_prefix_zero :
    (∑ x ∈ Finset.range 82,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (180 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (180 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_180_suffix_zero :
    (∑ x ∈ Finset.range 46,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (180 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_180 :
    recurrence2B5A5.coeff 180 =
      ((220688535630019188077025806541585528267101162993529 * 10 ^ 70 +
        6079748339094371980909447489436145870791717576738895337518850105147701) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 181 = 82 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 21 +
      46 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_180_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_180_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_181_prefix_zero :
    (∑ x ∈ Finset.range 83,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (181 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (181 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_181_suffix_zero :
    (∑ x ∈ Finset.range 47,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (181 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_181 :
    recurrence2B5A5.coeff 181 =
      -((314123646666485604440753544055749747628593804491032 * 10 ^ 70 +
        9844261471080193043643259040809474821869362698884973669400878677969663) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 182 = 83 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 20 +
      47 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_181_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_181_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_182_prefix_zero :
    (∑ x ∈ Finset.range 84,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (182 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (182 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_182_suffix_zero :
    (∑ x ∈ Finset.range 48,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (182 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_182 :
    recurrence2B5A5.coeff 182 =
      ((129610169257758281812656635969602764774613669964118 * 10 ^ 70 +
        0786863363147181389921568933858993307709366894649312935620072537633670) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 183 = 84 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 19 +
      48 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_182_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_182_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_183_prefix_zero :
    (∑ x ∈ Finset.range 85,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (183 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (183 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_183_suffix_zero :
    (∑ x ∈ Finset.range 49,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (183 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_183 :
    recurrence2B5A5.coeff 183 =
      -((37449517741539888528515585121180099819333577095602 * 10 ^ 70 +
        1223174667537092550052377350495644303880289780640852720884398789433959) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 184 = 85 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 18 +
      49 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_183_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_183_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_184_prefix_zero :
    (∑ x ∈ Finset.range 86,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (184 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (184 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_184_suffix_zero :
    (∑ x ∈ Finset.range 50,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (184 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_184 :
    recurrence2B5A5.coeff 184 =
      ((8336930703580920543561281382089166105903633195264 * 10 ^ 70 +
        4380308465985345739947926914526141281538976786164460780999091285490443) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 185 = 86 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 17 +
      50 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_184_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_184_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_185_prefix_zero :
    (∑ x ∈ Finset.range 87,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (185 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (185 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_185_suffix_zero :
    (∑ x ∈ Finset.range 51,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (185 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_185 :
    recurrence2B5A5.coeff 185 =
      -((1394019968598910021949220606435100657081021785946 * 10 ^ 70 +
        5522863993779665746914735347521911921217968416140334419134405032306514) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 186 = 87 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 16 +
      51 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_185_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_185_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_186_prefix_zero :
    (∑ x ∈ Finset.range 88,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (186 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (186 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_186_suffix_zero :
    (∑ x ∈ Finset.range 52,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (186 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_186 :
    recurrence2B5A5.coeff 186 =
      ((140645446988531119719001924961257696384469636477 * 10 ^ 70 +
        1959813720616926907410142570579329141454861372945972485216688492062889) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 187 = 88 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 15 +
      52 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_186_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_186_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_187_prefix_zero :
    (∑ x ∈ Finset.range 89,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (187 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (187 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_187_suffix_zero :
    (∑ x ∈ Finset.range 53,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (187 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_187 :
    recurrence2B5A5.coeff 187 =
      ((7045040302098309440176425153243645447417333812 * 10 ^ 70 +
        4546365733788993513835514009805224078989818000370631989885482110901672) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 188 = 89 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 14 +
      53 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_187_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_187_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_188_prefix_zero :
    (∑ x ∈ Finset.range 90,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (188 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (188 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_188_suffix_zero :
    (∑ x ∈ Finset.range 54,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (188 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_188 :
    recurrence2B5A5.coeff 188 =
      -((7271361280006741620864297116686179761642257990 * 10 ^ 70 +
        2725044201512930144664466912872559609044517187903680387679318244054230) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 189 = 90 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 13 +
      54 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_188_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_188_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_189_prefix_zero :
    (∑ x ∈ Finset.range 91,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (189 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (189 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_189_suffix_zero :
    (∑ x ∈ Finset.range 55,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (189 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_189 :
    recurrence2B5A5.coeff 189 =
      ((1969455556162122745924130424320397789189267149 * 10 ^ 70 +
        4067425776415279053976773168543013042885924222650141139246817029572351) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 190 = 91 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 12 +
      55 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_189_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_189_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_190_prefix_zero :
    (∑ x ∈ Finset.range 92,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (190 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (190 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_190_suffix_zero :
    (∑ x ∈ Finset.range 56,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (190 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_190 :
    recurrence2B5A5.coeff 190 =
      -((349148242103567956460855304370865506344404839 * 10 ^ 70 +
        7824557647983639638950737773145291744023406577555925904104153194285777) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 191 = 92 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 11 +
      56 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_190_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_190_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_191_prefix_zero :
    (∑ x ∈ Finset.range 93,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (191 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (191 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_191_suffix_zero :
    (∑ x ∈ Finset.range 57,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (191 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_191 :
    recurrence2B5A5.coeff 191 =
      ((42202240919709485453596158744773289710320561 * 10 ^ 70 +
        3281811942971197333520642553388089019186578313237034565731433717978842) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 192 = 93 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 10 +
      57 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_191_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_191_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_192_prefix_zero :
    (∑ x ∈ Finset.range 94,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (192 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (192 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_192_suffix_zero :
    (∑ x ∈ Finset.range 58,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (192 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_192 :
    recurrence2B5A5.coeff 192 =
      -((2547735052055596756079375294623372537518407 * 10 ^ 70 +
        9760378638113871111464052477175914575431669587004955199692147371798433) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 193 = 94 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 9 +
      58 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_192_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_192_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_193_prefix_zero :
    (∑ x ∈ Finset.range 95,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (193 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (193 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_193_suffix_zero :
    (∑ x ∈ Finset.range 59,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (193 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_193 :
    recurrence2B5A5.coeff 193 =
      -((246118157511574268138095826320703648465070 * 10 ^ 70 +
        1015907610132757058490813459427526105004543115443554916569074384544771) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 194 = 95 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 8 +
      59 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_193_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_193_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_194_prefix_zero :
    (∑ x ∈ Finset.range 96,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (194 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (194 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_194_suffix_zero :
    (∑ x ∈ Finset.range 60,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (194 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_194 :
    recurrence2B5A5.coeff 194 =
      ((93992511154313650107373356945329907276479 * 10 ^ 70 +
        8809769674028143621073672385275944277991183139940796911601407429506578) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 195 = 96 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 7 +
      60 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_194_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_194_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_195_prefix_zero :
    (∑ x ∈ Finset.range 97,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (195 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (195 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_195_suffix_zero :
    (∑ x ∈ Finset.range 61,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (195 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_195 :
    recurrence2B5A5.coeff 195 =
      -((14153236388243137952880475325109521793518 * 10 ^ 70 +
        1585937257492641984215667823907352332803344266529806529502781682518066) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 196 = 97 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 6 +
      61 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_195_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_195_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_196_prefix_zero :
    (∑ x ∈ Finset.range 98,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (196 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (196 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_196_suffix_zero :
    (∑ x ∈ Finset.range 62,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (196 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_196 :
    recurrence2B5A5.coeff 196 =
      ((1242350220787096967785004541583433298486 * 10 ^ 70 +
        4988422011300904308336771682161905400483373025624265639364402357296320) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 197 = 98 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 5 +
      62 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_196_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_196_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_197_prefix_zero :
    (∑ x ∈ Finset.range 99,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (197 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (197 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_197_suffix_zero :
    (∑ x ∈ Finset.range 63,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (197 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_197 :
    recurrence2B5A5.coeff 197 =
      -((39180630515027524310712879890681276496 * 10 ^ 70 +
        3909050657575645974560978151893951369820234952326118619614176771678863) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 198 = 99 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 4 +
      63 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_197_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_197_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_198_prefix_zero :
    (∑ x ∈ Finset.range 100,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (198 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (198 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_198_suffix_zero :
    (∑ x ∈ Finset.range 64,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (198 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_198 :
    recurrence2B5A5.coeff 198 =
      -((6071559239363060106785981334306409753 * 10 ^ 70 +
        5398083183370623492976689516179067992258160451970799692436123016830022) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 199 = 100 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 3 +
      64 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_198_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_198_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_199_prefix_zero :
    (∑ x ∈ Finset.range 101,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (199 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (199 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_199_suffix_zero :
    (∑ x ∈ Finset.range 65,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (199 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_199 :
    recurrence2B5A5.coeff 199 =
      ((1068247939634884782456620841318081550 * 10 ^ 70 +
        0514483720870887331739945856463355838055386897875545414055102412252132) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 200 = 101 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 2 +
      65 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_199_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_199_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_200_prefix_zero :
    (∑ x ∈ Finset.range 102,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (200 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (200 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_200_suffix_zero :
    (∑ x ∈ Finset.range 66,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (200 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_200 :
    recurrence2B5A5.coeff 200 =
      -((78160995504168717437949561779933756 * 10 ^ 70 +
        4054926407005589569244237168490269233287224249407792347378949172309505) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 201 = 102 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 1 +
      66 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_200_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_200_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_201_prefix_zero :
    (∑ x ∈ Finset.range 103,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (201 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (201 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_201_suffix_zero :
    (∑ x ∈ Finset.range 67,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (201 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_201 :
    recurrence2B5A5.coeff 201 =
      ((1730048054778737671349856631330205 * 10 ^ 70 +
        3848427805824495038802543144386363311956178613225807424850122079643874) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 202 = 103 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_201_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_201_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_202_prefix_zero :
    (∑ x ∈ Finset.range 104,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (202 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (202 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_202_suffix_zero :
    (∑ x ∈ Finset.range 68,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (202 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_202 :
    recurrence2B5A5.coeff 202 =
      ((204034497266724750862656476574665 * 10 ^ 70 +
        3355867102318132952799717358110414307044603816693112089573267619961852) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 203 = 104 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 31 +
      68 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_202_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_202_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_203_prefix_zero :
    (∑ x ∈ Finset.range 105,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (203 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (203 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_203_suffix_zero :
    (∑ x ∈ Finset.range 69,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (203 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_203 :
    recurrence2B5A5.coeff 203 =
      -((20612313305516690567747711860799 * 10 ^ 70 +
        7230308731295885494331970438510650676669158338015520608378486400950499) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 204 = 105 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 30 +
      69 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_203_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_203_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_204_prefix_zero :
    (∑ x ∈ Finset.range 106,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (204 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (204 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_204_suffix_zero :
    (∑ x ∈ Finset.range 70,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (204 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_204 :
    recurrence2B5A5.coeff 204 =
      ((630281626675886773609982451778 * 10 ^ 70 +
        1386499228021273131459329905152231574102089510931220897857479870419749) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 205 = 106 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 29 +
      70 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_204_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_204_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_205_prefix_zero :
    (∑ x ∈ Finset.range 107,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (205 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (205 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_205_suffix_zero :
    (∑ x ∈ Finset.range 71,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (205 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_205 :
    recurrence2B5A5.coeff 205 =
      ((15428696143066533574880343833 * 10 ^ 70 +
        1407149809084184627844649073346534934326384979758956408705194650272665) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 206 = 107 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 28 +
      71 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_205_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_205_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_206_prefix_zero :
    (∑ x ∈ Finset.range 108,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (206 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (206 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_206_suffix_zero :
    (∑ x ∈ Finset.range 72,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (206 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_206 :
    recurrence2B5A5.coeff 206 =
      -((1629304320782318618716345362 * 10 ^ 70 +
        3282924543958298520555060175625444421939724584557077433335385018337113) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 207 = 108 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 27 +
      72 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_206_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_206_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_207_prefix_zero :
    (∑ x ∈ Finset.range 109,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (207 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (207 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_207_suffix_zero :
    (∑ x ∈ Finset.range 73,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (207 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_207 :
    recurrence2B5A5.coeff 207 =
      ((27020529264836867674026136 * 10 ^ 70 +
        3407320299091791478566809327510855125192573572874350899334295019743677) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 208 = 109 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 26 +
      73 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_207_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_207_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_208_prefix_zero :
    (∑ x ∈ Finset.range 110,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (208 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (208 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_208_suffix_zero :
    (∑ x ∈ Finset.range 74,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (208 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_208 :
    recurrence2B5A5.coeff 208 =
      ((885238383063937365790665 * 10 ^ 70 +
        0890184902172044604446739746808938348752801548818551304497770690274655) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 209 = 110 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 25 +
      74 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_208_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_208_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_209_prefix_zero :
    (∑ x ∈ Finset.range 111,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (209 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (209 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_209_suffix_zero :
    (∑ x ∈ Finset.range 75,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (209 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_209 :
    recurrence2B5A5.coeff 209 =
      -((28464735335564663097533 * 10 ^ 70 +
        2120129000869000421640880551360150463348800030452316980102123136742999) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 210 = 111 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 24 +
      75 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_209_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_209_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_210_prefix_zero :
    (∑ x ∈ Finset.range 112,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (210 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (210 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_210_suffix_zero :
    (∑ x ∈ Finset.range 76,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (210 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_210 :
    recurrence2B5A5.coeff 210 =
      -((121428171715428443955 * 10 ^ 70 +
        5308831206896571434101248353211616305720199861374736501020900282303830) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 211 = 112 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 23 +
      76 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_210_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_210_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_211_prefix_zero :
    (∑ x ∈ Finset.range 113,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (211 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (211 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_211_suffix_zero :
    (∑ x ∈ Finset.range 77,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (211 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_211 :
    recurrence2B5A5.coeff 211 =
      ((8000003564062630129 * 10 ^ 70 +
        1072428735813389262913428610086409181211631173445105867657636704324894) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 212 = 113 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 22 +
      77 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_211_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_211_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_212_prefix_zero :
    (∑ x ∈ Finset.range 114,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (212 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (212 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_212_suffix_zero :
    (∑ x ∈ Finset.range 78,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (212 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_212 :
    recurrence2B5A5.coeff 212 =
      ((6667149733609417 * 10 ^ 70 +
        7683782118665805562778812288405587186182330573713939342330760926296801) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 213 = 114 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 21 +
      78 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_212_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_212_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_213_prefix_zero :
    (∑ x ∈ Finset.range 115,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (213 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (213 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_213_suffix_zero :
    (∑ x ∈ Finset.range 79,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (213 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_213 :
    recurrence2B5A5.coeff 213 =
      -((837229976328711 * 10 ^ 70 +
        3708608716198212496760155968575481427729640925482720204763835829753790) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 214 = 115 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 20 +
      79 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_213_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_213_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_214_prefix_zero :
    (∑ x ∈ Finset.range 116,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (214 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (214 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_214_suffix_zero :
    (∑ x ∈ Finset.range 80,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (214 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_214 :
    recurrence2B5A5.coeff 214 =
      -((1150194700862 * 10 ^ 70 +
        7211815385818142308523730745936879093375620220260374456221468851440179) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 215 = 116 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 19 +
      80 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_214_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_214_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_215_prefix_zero :
    (∑ x ∈ Finset.range 117,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (215 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (215 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_215_suffix_zero :
    (∑ x ∈ Finset.range 81,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (215 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_215 :
    recurrence2B5A5.coeff 215 =
      ((34023915890 * 10 ^ 70 +
        5851386290370559492904342596337569485747955386465953098881710874563979) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 216 = 117 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 18 +
      81 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_215_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_215_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_216_prefix_zero :
    (∑ x ∈ Finset.range 118,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (216 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (216 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_216_suffix_zero :
    (∑ x ∈ Finset.range 82,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (216 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_216 :
    recurrence2B5A5.coeff 216 =
      ((64250754 * 10 ^ 70 +
        1311005678125917278756788964454113918013840714334408935079632999822716) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 217 = 118 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 17 +
      82 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_216_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_216_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_217_prefix_zero :
    (∑ x ∈ Finset.range 119,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (217 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (217 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_217_suffix_zero :
    (∑ x ∈ Finset.range 83,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (217 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_217 :
    recurrence2B5A5.coeff 217 =
      -((555376 * 10 ^ 70 +
        1187060285924750180376912432689161227463802305237486228577602097297955) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 218 = 119 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 16 +
      83 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_217_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_217_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_218_prefix_zero :
    (∑ x ∈ Finset.range 120,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (218 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (218 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_218_suffix_zero :
    (∑ x ∈ Finset.range 84,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (218 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_218 :
    recurrence2B5A5.coeff 218 =
      -((935 * 10 ^ 70 +
        5795371096106573372887299832420474988709115996499856642685747796117245) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 219 = 120 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 15 +
      84 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_218_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_218_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_219_prefix_zero :
    (∑ x ∈ Finset.range 121,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (219 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (219 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_219_suffix_zero :
    (∑ x ∈ Finset.range 85,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (219 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_219 :
    recurrence2B5A5.coeff 219 =
      ((4 * 10 ^ 70 +
        3970408537271538877536147239046343874458798692036138828397822447884816) : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 220 = 121 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 14 +
      85 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_219_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_219_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2B5A5_coeff_220_prefix_zero :
    (∑ x ∈ Finset.range 122,
      remainder3Coefficient5.coeff x * remainder2Coefficient5.coeff (220 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A5_coeff_high (220 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2B5A5_coeff_220_suffix_zero :
    (∑ x ∈ Finset.range 86,
      remainder3Coefficient5.coeff (135 + x) *
        remainder2Coefficient5.coeff (220 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2B5A5_coeff_220 :
    recurrence2B5A5.coeff 220 =
      (41437633035796276550795972156754284418344811110145717032823462056508 : ℚ) := by
  unfold recurrence2B5A5
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 221 = 122 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 13 +
      86 by norm_num, Finset.sum_range_add]
  rw [recurrence2B5A5_coeff_220_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2B5A5_coeff_220_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
