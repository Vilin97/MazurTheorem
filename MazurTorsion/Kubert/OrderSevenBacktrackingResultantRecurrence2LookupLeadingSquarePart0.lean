/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB5
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: LeadingSquare coefficient convolution

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

theorem recurrence2LeadingSquare_coeff_0 :
    recurrence2LeadingSquare.coeff 0 =
      (4096 : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_1 :
    recurrence2LeadingSquare.coeff 1 =
      (-1555968 : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_2 :
    recurrence2LeadingSquare.coeff 2 =
      (173531730192 : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_3 :
    recurrence2LeadingSquare.coeff 3 =
      (-99284860407600 : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_4 :
    recurrence2LeadingSquare.coeff 4 =
      (1922392753113905604 : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_5 :
    recurrence2LeadingSquare.coeff 5 =
      (-1438742654696290875232 : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_6 :
    recurrence2LeadingSquare.coeff 6 =
      (1863311887180376241076440 : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_7 :
    recurrence2LeadingSquare.coeff 7 =
      (-1034916299402820150501916880 : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_8 :
    recurrence2LeadingSquare.coeff 8 =
      (599843957166365418574143949196 : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_9 :
    recurrence2LeadingSquare.coeff 9 =
      (-231837150853507546031805458369756 : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_10 :
    recurrence2LeadingSquare.coeff 10 =
      (70748550007318215530341904478201924 : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_11 :
    recurrence2LeadingSquare.coeff 11 =
      (-16377455483128575823415601197313151212 : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_12 :
    recurrence2LeadingSquare.coeff 12 =
      (3024973294940718459127631084538949238228 : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_13 :
    recurrence2LeadingSquare.coeff 13 =
      (-446439313674927150719615688839969928008852 : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_14 :
    recurrence2LeadingSquare.coeff 14 =
      (53562293848573888568410189832336706738863545 : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_15 :
    recurrence2LeadingSquare.coeff 15 =
      (-5263628285951024367685081149476342859270224830 : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_16 :
    recurrence2LeadingSquare.coeff 16 =
      (428418678920886674821768830626837678950757033669 : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_17 :
    recurrence2LeadingSquare.coeff 17 =
      (-29088271130254720787808348406322930881548928914024 : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_18 :
    recurrence2LeadingSquare.coeff 18 =
      (1656098930124530654497011715217891691405298437260086 : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_19 :
    recurrence2LeadingSquare.coeff 19 =
      (-78618047501288122379065927173442983805033661057132738 : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_20 :
    recurrence2LeadingSquare.coeff 20 =
      (3000605181584223092537705329306074589411769526567330554 : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_21 :
    recurrence2LeadingSquare.coeff 21 =
      (-78285615043618307479386608467173936895042044729004895848 : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_22 :
    recurrence2LeadingSquare.coeff 22 =
      (-72397998627720587945454512726589116106947046833913277715 : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_23 :
    recurrence2LeadingSquare.coeff 23 =
      (176108286663937982352109677361722544863605249530646409058664 : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_24 :
    recurrence2LeadingSquare.coeff 24 =
      (-14208040997285836710944735093707236908243364347917983238286010 : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_25 :
    recurrence2LeadingSquare.coeff 25 =
      (781193829976591951776804191692890301470387188918380576779810194 : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_26 :
    recurrence2LeadingSquare.coeff 26 =
      (-34034748746878105739823147823072336190669282113251729184687964229 : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_27 :
    recurrence2LeadingSquare.coeff 27 =
      (1202072385797189122518701258725931151583279352612921482604713901230 : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_28 :
    recurrence2LeadingSquare.coeff 28 =
      (-32485380623456132758842202488029802249117307560793426782234383067965 : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_29 :
    recurrence2LeadingSquare.coeff 29 =
      (470385138190939287162565606258071646786611090584086425085347097474682 : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_30 :
    recurrence2LeadingSquare.coeff 30 =
      ((1 * 10 ^ 70 +
        4174417140336370287313557288715394986268578323455892420469825428678697) : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_31 :
    recurrence2LeadingSquare.coeff 31 =
      -((157 * 10 ^ 70 +
        1521662967724245987560395989198441585873520014510887910580876734621824) : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_32 :
    recurrence2LeadingSquare.coeff 32 =
      ((8306 * 10 ^ 70 +
        9451137282270090890824420171278551854200274446407526052577645967124855) : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_33 :
    recurrence2LeadingSquare.coeff 33 =
      -((332253 * 10 ^ 70 +
        9554158016061556869642763499406756607254136093338406518581905913056068) : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_34 :
    recurrence2LeadingSquare.coeff 34 =
      ((10998124 * 10 ^ 70 +
        9281371399504220421643476805465813176352778206521763522744160738478441) : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_35 :
    recurrence2LeadingSquare.coeff 35 =
      -((310533145 * 10 ^ 70 +
        9509604684241636551827803173825658170604041797034761636467684047037898) : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_36 :
    recurrence2LeadingSquare.coeff 36 =
      ((7552970313 * 10 ^ 70 +
        5668872902576711565584354905403331773267132224554792226414494305837591) : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_37 :
    recurrence2LeadingSquare.coeff 37 =
      -((157838935196 * 10 ^ 70 +
        4110416614298779101955688842751412107648011018349341174949971136009008) : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_38 :
    recurrence2LeadingSquare.coeff 38 =
      ((2783867644641 * 10 ^ 70 +
        2606688944115780958307951310019451682914898452285520552314602964468579) : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_39 :
    recurrence2LeadingSquare.coeff 39 =
      -((39355048733997 * 10 ^ 70 +
        4089450770643641977579652759776565905534424693521370475270740367031564) : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_40 :
    recurrence2LeadingSquare.coeff 40 =
      ((371488439385395 * 10 ^ 70 +
        1797560907500689696481963661390335149459325194418901571297434997584338) : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_41 :
    recurrence2LeadingSquare.coeff 41 =
      ((415525739727202 * 10 ^ 70 +
        2144595899215620898747273242761327052287291877986732684770834481639808) : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_42 :
    recurrence2LeadingSquare.coeff 42 =
      -((119726167015602386 * 10 ^ 70 +
        7167402319074167035040937943970632166212613896834812718667040628860743) : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_43 :
    recurrence2LeadingSquare.coeff 43 =
      ((3410558442406656267 * 10 ^ 70 +
        1640755740780323600107327021860769621866059705754146812268097147138824) : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_44 :
    recurrence2LeadingSquare.coeff 44 =
      -((66976207024820589621 * 10 ^ 70 +
        7517204376090625438687623062290810287702100420304753709081527976360783) : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_45 :
    recurrence2LeadingSquare.coeff 45 =
      ((1045468359101359221290 * 10 ^ 70 +
        6227317008034204717094790249760254580416355865542827550399172984074260) : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_46 :
    recurrence2LeadingSquare.coeff 46 =
      -((13243063703683876381112 * 10 ^ 70 +
        9812857944665116246287393183800426163619311333150894277629375709856202) : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_47 :
    recurrence2LeadingSquare.coeff 47 =
      ((128847130886487213506114 * 10 ^ 70 +
        6223743480654962396760165095371573910313747865350881889873928365415420) : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_48 :
    recurrence2LeadingSquare.coeff 48 =
      -((698844604935277074505877 * 10 ^ 70 +
        5557942277353285540859351676307529020799928070701726018598877565364633) : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_49 :
    recurrence2LeadingSquare.coeff 49 =
      -((6178001483692798900195469 * 10 ^ 70 +
        3561205526239217686734869547021225337742826553960191046565040324035458) : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_50 :
    recurrence2LeadingSquare.coeff 50 =
      ((267851265930608362766823765 * 10 ^ 70 +
        6394578001481986028450203038898422013894242453235203878309199685875604) : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_51 :
    recurrence2LeadingSquare.coeff 51 =
      -((5293275131030408333245098956 * 10 ^ 70 +
        7938295791290922159723572264745581387552068367383832731706793464275358) : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_52 :
    recurrence2LeadingSquare.coeff 52 =
      ((80849762172713013140727974537 * 10 ^ 70 +
        2408657650770764971171018310486937620684736365901559736667519328543010) : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_53 :
    recurrence2LeadingSquare.coeff 53 =
      -((1058163062334017885810489986108 * 10 ^ 70 +
        8422631246069707343189010792421303109252873646690103734809259666168658) : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_54 :
    recurrence2LeadingSquare.coeff 54 =
      ((12348480047993925336174065528903 * 10 ^ 70 +
        0576629658785834264169605042380579515051565171779052947222999944740199) : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_55 :
    recurrence2LeadingSquare.coeff 55 =
      -((131088629799897886661737934903598 * 10 ^ 70 +
        4735547557104605679105458211957155692240202532723629873693111200084158) : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_56 :
    recurrence2LeadingSquare.coeff 56 =
      ((1280895964528849715633439720128879 * 10 ^ 70 +
        3842070335167895589021269134626629848765557495871873093561859475547595) : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_57 :
    recurrence2LeadingSquare.coeff 57 =
      -((11608108126121601700947196155353258 * 10 ^ 70 +
        9027267102560515145204603567953630846923225521605246441600182596520496) : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_58 :
    recurrence2LeadingSquare.coeff 58 =
      ((98080788734109460575871904037113393 * 10 ^ 70 +
        1935328300102984172560685656965828206628224101546289837916468016095813) : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_59 :
    recurrence2LeadingSquare.coeff 59 =
      -((775562526399301848020052831739815181 * 10 ^ 70 +
        4480056070145193933700798181834131874030693172868273142420574193783524) : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_60 :
    recurrence2LeadingSquare.coeff 60 =
      ((5755208642294814842225106502462709405 * 10 ^ 70 +
        7481072002904497817340773231477104095205509519830328031035957958364037) : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_61 :
    recurrence2LeadingSquare.coeff 61 =
      -((40160560921477053672112120169273364271 * 10 ^ 70 +
        4602529667813167330035783660880268422258899800649414838342009479546790) : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_62 :
    recurrence2LeadingSquare.coeff 62 =
      ((263915121917746405481939855001465934418 * 10 ^ 70 +
        3031883341364414821796392378439863772744642306193339303348604456572772) : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_63 :
    recurrence2LeadingSquare.coeff 63 =
      -((1634817173734795263594165501647317205063 * 10 ^ 70 +
        2768600591047498267573168398937253501450434505691710306846943635469404) : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_64 :
    recurrence2LeadingSquare.coeff 64 =
      ((9550464496968238704169421669395631292718 * 10 ^ 70 +
        8827345141334011721148763810645622681937071663613558398722770668755916) : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_65 :
    recurrence2LeadingSquare.coeff 65 =
      -((52617169760471667186265357718466252878641 * 10 ^ 70 +
        8528078631963464413307046195903810065285998068709299681625230119047960) : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_66 :
    recurrence2LeadingSquare.coeff 66 =
      ((273232480379004278969324189742715364743354 * 10 ^ 70 +
        5013056499110798887809750099451143721809639902475992064162185050593402) : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_67 :
    recurrence2LeadingSquare.coeff 67 =
      -((1335639133948980027770532000948988116596887 * 10 ^ 70 +
        5388675293216982800472220246011483064497351373622458171126164055128418) : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_68 :
    recurrence2LeadingSquare.coeff 68 =
      ((6132460389253774123652130615339235729409714 * 10 ^ 70 +
        5149048590727623313328962004695950099862341558892047890669969383745405) : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_69 :
    recurrence2LeadingSquare.coeff 69 =
      -((26351006467404195298452453948858415151938596 * 10 ^ 70 +
        8249030539384162825893376622540443472371446873781857386496782918710728) : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_70 :
    recurrence2LeadingSquare.coeff 70 =
      ((105348722951499375653161677573669830484378021 * 10 ^ 70 +
        1821039288494139630098420433588270121032715645108196421537094891007055) : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_71 :
    recurrence2LeadingSquare.coeff 71 =
      -((388028242238821340730553354727577567060511186 * 10 ^ 70 +
        2707092909904867338331237487771276753641204764540033520211962492285336) : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_72 :
    recurrence2LeadingSquare.coeff 72 =
      ((1293602944528889884162709775383806669112665908 * 10 ^ 70 +
        7646437120224616237950747276546660762296779643912269586766626848773691) : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_73 :
    recurrence2LeadingSquare.coeff 73 =
      -((3763545968787821543587994856682306872716793432 * 10 ^ 70 +
        5027575239949270790827054896199590020819042437338459823274508851123540) : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_74 :
    recurrence2LeadingSquare.coeff 74 =
      ((8680145385371938171972953493265924375080815283 * 10 ^ 70 +
        5857867358003885750600497454234662049660523643191287019107424548657741) : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_75 :
    recurrence2LeadingSquare.coeff 75 =
      -((9871614818651339553615707299423725501919813510 * 10 ^ 70 +
        3394140211426548228484229263726621100904064815358999145692622011769644) : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_76 :
    recurrence2LeadingSquare.coeff 76 =
      -((44347703838688118520229489247843715779380349998 * 10 ^ 70 +
        5412628875549692398327822029357448022002989437309526965787755494141073) : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_77 :
    recurrence2LeadingSquare.coeff 77 =
      ((414570574233139036281256807008632706571190345195 * 10 ^ 70 +
        0341855366747830132604406938232013616050497798705890769374706532669588) : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_78 :
    recurrence2LeadingSquare.coeff 78 =
      -((2158341869657888603881486360852943837414947809262 * 10 ^ 70 +
        9528067030786236831608033432413046704475058723573074174575705619465384) : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_79 :
    recurrence2LeadingSquare.coeff 79 =
      ((8963401137461205672479664806541636092235091337255 * 10 ^ 70 +
        4076671006342973751171401450043981375235247290542393092382503642002020) : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_80 :
    recurrence2LeadingSquare.coeff 80 =
      -((32043166600665066719638788264208854106912935523111 * 10 ^ 70 +
        7395486203109865047157114230032822927639068249024762276866432752719053) : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_81 :
    recurrence2LeadingSquare.coeff 81 =
      ((100695416808995487249058299938412708962883902964772 * 10 ^ 70 +
        5794488417445331144061952556682749865155363297010050525501992912321150) : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_82 :
    recurrence2LeadingSquare.coeff 82 =
      -((276692179424274851462595490576101049278328655088164 * 10 ^ 70 +
        1354103680010779920919344092407128646384450112747943498031227235375020) : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_83 :
    recurrence2LeadingSquare.coeff 83 =
      ((640615451172545569632303348962096756149776033715726 * 10 ^ 70 +
        7548128511013012587572551108297802066124054449931633764579823455606784) : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_84 :
    recurrence2LeadingSquare.coeff 84 =
      -((1096871126778262059890297574072078631353932614293008 * 10 ^ 70 +
        6771735301325154930882552431622484165421539258578449271105581702902500) : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_85 :
    recurrence2LeadingSquare.coeff 85 =
      ((447823119623887092291819753955925941593118083211088 * 10 ^ 70 +
        0092506850739520626849316946360800645403489043076685809798638662305704) : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_86 :
    recurrence2LeadingSquare.coeff 86 =
      ((6956120909074875926599966405556714023284254511716659 * 10 ^ 70 +
        7587373399581388741157141403397718029023418573004214429138651166397446) : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_87 :
    recurrence2LeadingSquare.coeff 87 =
      -((41733982647600763559981219919986753420194451324352158 * 10 ^ 70 +
        4208882280723070258947994951781905089017738852859077927569066402981914) : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_88 :
    recurrence2LeadingSquare.coeff 88 =
      ((169377959112703663306835312213923937133674076204924796 * 10 ^ 70 +
        8669955828696656174451381023929606378100445854743271606184156669242396) : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_89 :
    recurrence2LeadingSquare.coeff 89 =
      -((576382188798410550490011273942201107887120543766037542 * 10 ^ 70 +
        1697038421728060281830459005965511767574648844884788458995190312105458) : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_90 :
    recurrence2LeadingSquare.coeff 90 =
      ((1726776630082999755390513889186366453916649304148115484 * 10 ^ 70 +
        3784381207204048327992502323492092713700692262487022069259266094715438) : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_91 :
    recurrence2LeadingSquare.coeff 91 =
      -((4520227572146493299628978335520852711017801208029590965 * 10 ^ 70 +
        0248444835965439937760819093883945412465095007148862432379767471292748) : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_92 :
    recurrence2LeadingSquare.coeff 92 =
      ((9755994499721447375713123418267750730351600192585823690 * 10 ^ 70 +
        1370841004737340201496213923559636990391813701311531225618980869413080) : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_93 :
    recurrence2LeadingSquare.coeff 93 =
      -((14791499408283347235846431476691305374994269627289950865 * 10 ^ 70 +
        6334204677044522208062552197323478487285049151377301106724255854178970) : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_94 :
    recurrence2LeadingSquare.coeff 94 =
      ((7228412933024815289000831270082507801533005704900853426 * 10 ^ 70 +
        3975250301781278963066693855519379646322760042884583184057244739077729) : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_95 :
    recurrence2LeadingSquare.coeff 95 =
      ((14480952329981992621887154491045738980743143662431877221 * 10 ^ 70 +
        5499130067765030638384359453607555109127628778377152000055068288504864) : ℚ) := by
  unfold recurrence2LeadingSquare
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

theorem recurrence2LeadingSquare_coeff_96 :
    recurrence2LeadingSquare.coeff 96 =
      ((157846186778598447908164418970692465306467415584558434727 * 10 ^ 70 +
        8128447157884899476689042547928480677143660965109184228561630879825972) : ℚ) := by
  unfold recurrence2LeadingSquare
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
  norm_num [Finset.sum_range_succ]

theorem recurrence2LeadingSquare_coeff_97 :
    recurrence2LeadingSquare.coeff 97 =
      -((1670429066990176734232327998742154398578612149133627457689 * 10 ^ 70 +
        3720401662922000921343488847023861156470370919124917429576305220827090) : ℚ) := by
  unfold recurrence2LeadingSquare
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
  norm_num [Finset.sum_range_succ]

theorem recurrence2LeadingSquare_coeff_98 :
    recurrence2LeadingSquare.coeff 98 =
      ((7725143053335460835965367296797683514233644579300017387671 * 10 ^ 70 +
        5067911669526184849763609866155337930041890431314384270076861332236055) : ℚ) := by
  unfold recurrence2LeadingSquare
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
  norm_num [Finset.sum_range_succ]

theorem recurrence2LeadingSquare_coeff_99 :
    recurrence2LeadingSquare.coeff 99 =
      -((20603394452310131154964617401398347196975129439636699403343 * 10 ^ 70 +
        1785996162018714235616266223468497153518629961363489912641374411728908) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 100 = 0 +
    100 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  norm_num [Finset.sum_range_succ]

theorem recurrence2LeadingSquare_coeff_100 :
    recurrence2LeadingSquare.coeff 100 =
      ((15261406093131292905059057272689885263933029884955280910443 * 10 ^ 70 +
        1342865675694480756557780616720085523959343634311884784694203106923463) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 101 = 0 +
    101 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  norm_num [Finset.sum_range_succ]

theorem recurrence2LeadingSquare_coeff_101 :
    recurrence2LeadingSquare.coeff 101 =
      ((163356324785470515027778279245006027767206694934607601267964 * 10 ^ 70 +
        3113176368620682901699138952626392676860522829638632025940592993443346) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 102 = 0 +
    102 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 102 = 32 +
      70 by norm_num, Finset.sum_range_add]
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

theorem recurrence2LeadingSquare_coeff_102 :
    recurrence2LeadingSquare.coeff 102 =
      -((1102326691753237734382163760530621342138217551764984257815714 * 10 ^ 70 +
        9727736450256423514491544259336255439251458689412594182561213377916927) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 103 = 0 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
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

theorem recurrence2LeadingSquare_coeff_103 :
    recurrence2LeadingSquare.coeff 103 =
      ((4584396483976878663569583194660126858025253455187353860826006 * 10 ^ 70 +
        0475075755888784775599454846323587853086065878876688810808467747032230) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 104 = 0 +
    104 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 104 = 32 +
      72 by norm_num, Finset.sum_range_add]
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

theorem recurrence2LeadingSquare_coeff_104 :
    recurrence2LeadingSquare.coeff 104 =
      -((14548421100598952294859432809750726934168811060316681742443453 * 10 ^ 70 +
        6097275216637973005367129975542385059472830216365693168472744855537050) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 105 = 0 +
    105 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 105 = 32 +
      73 by norm_num, Finset.sum_range_add]
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

theorem recurrence2LeadingSquare_coeff_105 :
    recurrence2LeadingSquare.coeff 105 =
      ((29373365727822772651315534907765947170908203867612735218605949 * 10 ^ 70 +
        9441111297606913566222959716387382354545305151612205724482111473981622) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 106 = 0 +
    106 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 106 = 32 +
      74 by norm_num, Finset.sum_range_add]
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

theorem recurrence2LeadingSquare_coeff_106 :
    recurrence2LeadingSquare.coeff 106 =
      ((33119853375609169307101594881972325381718010916073502782035683 * 10 ^ 70 +
        9981087170846709784090457454395853809781705476415923588685033252816250) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 107 = 0 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
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

theorem recurrence2LeadingSquare_coeff_107 :
    recurrence2LeadingSquare.coeff 107 =
      -((685284804867397969506277035574958163410462114861229669519407748 * 10 ^ 70 +
        7365007408015039121316552526604154693879845086650303244501712971096492) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 108 = 0 +
    108 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 108 = 32 +
      76 by norm_num, Finset.sum_range_add]
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

theorem recurrence2LeadingSquare_coeff_108 :
    recurrence2LeadingSquare.coeff 108 =
      ((3743093430141601083750949604430527541968293612345933606710459077 * 10 ^ 70 +
        7436505697414459669084226242535476828966221810251772086745659793612198) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 109 = 0 +
    109 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 109 = 32 +
      77 by norm_num, Finset.sum_range_add]
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

theorem recurrence2LeadingSquare_coeff_109 :
    recurrence2LeadingSquare.coeff 109 =
      -((12124058065726019354730138251233727366761802976115680870295572758 * 10 ^ 70 +
        8474091074526797743126596296322445472795872083649834876789133535575094) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 110 = 0 +
    110 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 110 = 32 +
      78 by norm_num, Finset.sum_range_add]
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

theorem recurrence2LeadingSquare_coeff_110 :
    recurrence2LeadingSquare.coeff 110 =
      ((17773536928767036460537532885963490567387372039480937327616296707 * 10 ^ 70 +
        6334235737908574609538108804047837503005640652103287609141659319344273) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 111 = 0 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
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

theorem recurrence2LeadingSquare_coeff_111 :
    recurrence2LeadingSquare.coeff 111 =
      ((52073771648209923075933990668844144266680550152265407245473791750 * 10 ^ 70 +
        4248707029660271032073164635585126160435931742792672014487583794933366) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 112 = 0 +
    112 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 112 = 32 +
      80 by norm_num, Finset.sum_range_add]
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

theorem recurrence2LeadingSquare_coeff_112 :
    recurrence2LeadingSquare.coeff 112 =
      -((439295910728159856955971496979837235606592925397556078319432121881 * 10 ^ 70 +
        7576975876066425738256229728570143708173586108439006319863296316067675) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 113 = 0 +
    113 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 113 = 32 +
      81 by norm_num, Finset.sum_range_add]
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

theorem recurrence2LeadingSquare_coeff_113 :
    recurrence2LeadingSquare.coeff 113 =
      ((1446903836750173139053468137495081414387795592654926675287977725060 * 10 ^ 70 +
        9537264637972036066516306319811442755068509019853484140107614297089066) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 114 = 0 +
    114 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
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

theorem recurrence2LeadingSquare_coeff_114 :
    recurrence2LeadingSquare.coeff 114 =
      -((2092866325862145812716324095455641809639770088505334894415880428798 * 10 ^ 70 +
        5755248581907852012935952901814775196365298190982278649910928645277364) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 115 = 0 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
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

theorem recurrence2LeadingSquare_coeff_115 :
    recurrence2LeadingSquare.coeff 115 =
      -((3307688722500730860915948909298574561245873549985076619759800432378 * 10 ^ 70 +
        4648429580238387640212392773461591125625320554605934272649794462494998) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 116 = 0 +
    116 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 116 = 32 +
      84 by norm_num, Finset.sum_range_add]
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

theorem recurrence2LeadingSquare_coeff_116 :
    recurrence2LeadingSquare.coeff 116 =
      ((22218468420369964324535673889224781727985507726600152421943770600965 * 10 ^ 70 +
        3977230501862702121561585632753289185806369088348618888042812324162710) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 117 = 0 +
    117 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 117 = 32 +
      85 by norm_num, Finset.sum_range_add]
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

theorem recurrence2LeadingSquare_coeff_117 :
    recurrence2LeadingSquare.coeff 117 =
      -((13055671636421636162079515526591490776496110134790595129118555889178 * 10 ^ 70 +
        9598392539234822003856857388930033038409510835697549023939940428901924) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 118 = 0 +
    118 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
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

theorem recurrence2LeadingSquare_coeff_118 :
    recurrence2LeadingSquare.coeff 118 =
      -((279779800014477396606459215756382846142641694873276805329868884778647 * 10 ^ 70 +
        8029528746635877991564320465931982263080230458347220807711243653454049) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 119 = 0 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
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

theorem recurrence2LeadingSquare_coeff_119 :
    recurrence2LeadingSquare.coeff 119 =
      ((1393319114033394439029819835769816224318705326995900886869257427694368 * 10 ^ 70 +
        8912501832527321760409916153879472697233542915138858094130767003822902) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 120 = 0 +
    120 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 120 = 32 +
      88 by norm_num, Finset.sum_range_add]
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

theorem recurrence2LeadingSquare_coeff_120 :
    recurrence2LeadingSquare.coeff 120 =
      -((2472438213610324242786198977464171957645031803439339978851413313679951 * 10 ^ 70 +
        2070755573060900821317347820743577414159782899862321451211016063898669) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 121 = 0 +
    121 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 121 = 32 +
      89 by norm_num, Finset.sum_range_add]
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

theorem recurrence2LeadingSquare_coeff_121 :
    recurrence2LeadingSquare.coeff 121 =
      -((6814088707675147899554930422067721085540997021707608564447334461376861 * 10 ^ 70 +
        5944475427116201893611318460546207823563924769082237679730582020349292) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 122 = 0 +
    122 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
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

theorem recurrence2LeadingSquare_coeff_122 :
    recurrence2LeadingSquare.coeff 122 =
      (((6 * 10 ^ 70 +
        3423570036753966360206743459199024000555822784112802400939567385026733) * 10 ^ 70 +
        0155210296633810079538353155240110984683065164021086506850098254003094) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 123 = 0 +
    123 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
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

theorem recurrence2LeadingSquare_coeff_123 :
    recurrence2LeadingSquare.coeff 123 =
      -(((22 * 10 ^ 70 +
        1960907548154617623545659641519969580531095315760597439535733178547826) * 10 ^ 70 +
        5366437919030372441789884648544813195800492198565141735401435334960000) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 124 = 0 +
    124 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 124 = 32 +
      92 by norm_num, Finset.sum_range_add]
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

theorem recurrence2LeadingSquare_coeff_124 :
    recurrence2LeadingSquare.coeff 124 =
      (((34 * 10 ^ 70 +
        9612944165184439303148036766982546315986163008374216009496531943587984) * 10 ^ 70 +
        6527635019298971556653511055679971263613145026873267892800930454289025) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 125 = 0 +
    125 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 125 = 32 +
      93 by norm_num, Finset.sum_range_add]
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

theorem recurrence2LeadingSquare_coeff_125 :
    recurrence2LeadingSquare.coeff 125 =
      (((63 * 10 ^ 70 +
        9719438783264085538409550553002109183745669353649001421797263542765112) * 10 ^ 70 +
        7682031645400903767994399767816405280865468604258427561526787346229610) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 126 = 0 +
    126 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 126 = 32 +
      94 by norm_num, Finset.sum_range_add]
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

theorem recurrence2LeadingSquare_coeff_126 :
    recurrence2LeadingSquare.coeff 126 =
      -(((604 * 10 ^ 70 +
        0615642135954055356341977900701838952077255321877669633645376833649151) * 10 ^ 70 +
        3619934009002787473999624522352534794405780449290125472679214555288911) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 127 = 0 +
    127 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
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

theorem recurrence2LeadingSquare_coeff_127 :
    recurrence2LeadingSquare.coeff 127 =
      (((1952 * 10 ^ 70 +
        1707632110454729277662781600251795563947306926103907226282384685516579) * 10 ^ 70 +
        6889755074215391479558761148607299224829114762974382057757384830627120) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 128 = 0 +
    128 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 128 = 32 +
      96 by norm_num, Finset.sum_range_add]
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

theorem recurrence2LeadingSquare_coeff_128 :
    recurrence2LeadingSquare.coeff 128 =
      -(((2613 * 10 ^ 70 +
        3545369177609399455890395614331703802246369704296182880269184418655870) * 10 ^ 70 +
        7283359220335406268953379690545375239934159721778095995408245147581345) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 129 = 0 +
    129 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 129 = 32 +
      97 by norm_num, Finset.sum_range_add]
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
  norm_num [Finset.sum_range_succ]

theorem recurrence2LeadingSquare_coeff_129 :
    recurrence2LeadingSquare.coeff 129 =
      -(((7091 * 10 ^ 70 +
        5691864577149768926810929255568430357691676325082267752345436059414901) * 10 ^ 70 +
        6336734843057492176949660243425412051882869500778933932767234410358566) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 130 = 0 +
    130 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 130 = 32 +
      98 by norm_num, Finset.sum_range_add]
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
  norm_num [Finset.sum_range_succ]

theorem recurrence2LeadingSquare_coeff_130 :
    recurrence2LeadingSquare.coeff 130 =
      (((55117 * 10 ^ 70 +
        5694623889764030871145432116318841685712692433020241134280636991406442) * 10 ^ 70 +
        5791031783297270032539055078284053524254708730354145637430735054371585) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 131 = 0 +
    131 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
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
  norm_num [Finset.sum_range_succ]

theorem recurrence2LeadingSquare_coeff_131 :
    recurrence2LeadingSquare.coeff 131 =
      -(((176760 * 10 ^ 70 +
        4034590504280409570926728531885847408550061124162402356471873642544606) * 10 ^ 70 +
        3587716140110992780900711070724538028297719863833485704742388558025464) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 132 = 0 +
    132 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  norm_num [Finset.sum_range_succ]

theorem recurrence2LeadingSquare_coeff_132 :
    recurrence2LeadingSquare.coeff 132 =
      (((286009 * 10 ^ 70 +
        2046735638879719840769902486434859493487410921943053844931752171039040) * 10 ^ 70 +
        9036110816913150421308376503012183185535325704814288243677816683952566) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 133 = 0 +
    133 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  norm_num [Finset.sum_range_succ]

theorem recurrence2LeadingSquare_coeff_133 :
    recurrence2LeadingSquare.coeff 133 =
      (((275662 * 10 ^ 70 +
        6186128227347169050744280682499727262922021103926008786179405074967604) * 10 ^ 70 +
        2641114264806503043557665585755214944560262949271222465890255445310792) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 134 = 0 +
    134 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 134 = 32 +
      102 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 102 = 32 +
      70 by norm_num, Finset.sum_range_add]
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

theorem recurrence2LeadingSquare_coeff_134 :
    recurrence2LeadingSquare.coeff 134 =
      -(((3623464 * 10 ^ 70 +
        5464072136910748223539869469800293570484387924943389890994291568748586) * 10 ^ 70 +
        4775821912114220047945951446925971448353991270267780694933629703020337) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 135 = 0 +
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
    rw [show 39 = 32 +
      7 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_135_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (135 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_135_suffix_zero :
    (∑ x ∈ Finset.range 1,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (135 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_135 :
    recurrence2LeadingSquare.coeff 135 =
      (((13590907 * 10 ^ 70 +
        4745195424752098118103703517193268842403414982506677004514271849854132) * 10 ^ 70 +
        1394167966908160736082283861410363808030843663674022193708770943967368) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 136 = 1 +
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
    rw [show 39 = 32 +
      7 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 7 = 6 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_135_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_135_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_136_prefix_zero :
    (∑ x ∈ Finset.range 2,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (136 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (136 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_136_suffix_zero :
    (∑ x ∈ Finset.range 2,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (136 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_136 :
    recurrence2LeadingSquare.coeff 136 =
      -(((30245024 * 10 ^ 70 +
        0413615064541133901438792852709589264407368312482878403665295029387273) * 10 ^ 70 +
        6922024675802288246888690380443452949953909323938873267433903664257660) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 137 = 2 +
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
    rw [show 39 = 32 +
      7 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 7 = 5 +
      2 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_136_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_136_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_137_prefix_zero :
    (∑ x ∈ Finset.range 3,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (137 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (137 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_137_suffix_zero :
    (∑ x ∈ Finset.range 3,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (137 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_137 :
    recurrence2LeadingSquare.coeff 137 =
      (((25007527 * 10 ^ 70 +
        7522352301898421103830143795787611488123060391563640800199516627574736) * 10 ^ 70 +
        5517742950918946852479265179109352711348131893297811516653471660136760) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 138 = 3 +
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
    rw [show 39 = 32 +
      7 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 7 = 4 +
      3 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_137_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_137_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_138_prefix_zero :
    (∑ x ∈ Finset.range 4,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (138 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (138 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_138_suffix_zero :
    (∑ x ∈ Finset.range 4,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (138 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_138 :
    recurrence2LeadingSquare.coeff 138 =
      (((124750169 * 10 ^ 70 +
        7215321067478409163691452154640468245967876360716674413920597722133017) * 10 ^ 70 +
        5010518363274600465709541149849203777141078740249228458145811924408812) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 139 = 4 +
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
    rw [show 39 = 32 +
      7 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 7 = 3 +
      4 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_138_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_138_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_139_prefix_zero :
    (∑ x ∈ Finset.range 5,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (139 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (139 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_139_suffix_zero :
    (∑ x ∈ Finset.range 5,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (139 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_139 :
    recurrence2LeadingSquare.coeff 139 =
      -(((738017727 * 10 ^ 70 +
        3947936090539073303376616748107206482061787932786178395077098356391322) * 10 ^ 70 +
        4216401372827148516844860012725962057969097247387769875756914183025586) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 140 = 5 +
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
    rw [show 39 = 32 +
      7 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 7 = 2 +
      5 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_139_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_139_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_140_prefix_zero :
    (∑ x ∈ Finset.range 6,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (140 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (140 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_140_suffix_zero :
    (∑ x ∈ Finset.range 6,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (140 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_140 :
    recurrence2LeadingSquare.coeff 140 =
      (((2318862789 * 10 ^ 70 +
        4228720405061066879614481958599753494807435633363267687624221435887136) * 10 ^ 70 +
        5778944569515939199929900980244875778131912911605879265443678989941987) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 141 = 6 +
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
    rw [show 39 = 32 +
      7 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 7 = 1 +
      6 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_140_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_140_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_141_prefix_zero :
    (∑ x ∈ Finset.range 7,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (141 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (141 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_141_suffix_zero :
    (∑ x ∈ Finset.range 7,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (141 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_141 :
    recurrence2LeadingSquare.coeff 141 =
      -(((4839192002 * 10 ^ 70 +
        1062759374922098142608987701986882614892218945552616525120573862564905) * 10 ^ 70 +
        5519709293228537002744909432556539322558955854168562518293379414331722) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 142 = 7 +
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
    rw [show 39 = 32 +
      7 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_141_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_141_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_142_prefix_zero :
    (∑ x ∈ Finset.range 8,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (142 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (142 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_142_suffix_zero :
    (∑ x ∈ Finset.range 8,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (142 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_142 :
    recurrence2LeadingSquare.coeff 142 =
      (((4809602106 * 10 ^ 70 +
        1338661827595414025462406821169814448229667671925164321375052813598835) * 10 ^ 70 +
        8212034820825667458635825776729392236312840385836440742362631072457931) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 143 = 8 +
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
    rw [show 39 = 31 +
      8 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_142_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_142_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_143_prefix_zero :
    (∑ x ∈ Finset.range 9,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (143 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (143 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_143_suffix_zero :
    (∑ x ∈ Finset.range 9,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (143 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_143 :
    recurrence2LeadingSquare.coeff 143 =
      (((12519173615 * 10 ^ 70 +
        4695317005208545369364065390327730318625002707922312563168684742511286) * 10 ^ 70 +
        8140394040176269186718330663406016538496013852635235241721014444096802) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 144 = 9 +
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
    rw [show 39 = 30 +
      9 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_143_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_143_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_144_prefix_zero :
    (∑ x ∈ Finset.range 10,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (144 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (144 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_144_suffix_zero :
    (∑ x ∈ Finset.range 10,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (144 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_144 :
    recurrence2LeadingSquare.coeff 144 =
      -(((88066892556 * 10 ^ 70 +
        7552921090909069505610040974415789009715718740905405632945626882074022) * 10 ^ 70 +
        5330248499955107861215400167035476019069401150292329679010738810568846) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 145 = 10 +
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
    rw [show 39 = 29 +
      10 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_144_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_144_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_145_prefix_zero :
    (∑ x ∈ Finset.range 11,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (145 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (145 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_145_suffix_zero :
    (∑ x ∈ Finset.range 11,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (145 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_145 :
    recurrence2LeadingSquare.coeff 145 =
      (((305432375529 * 10 ^ 70 +
        4087940249589223722023879402786940708439660669362923102388038121118301) * 10 ^ 70 +
        9890232713257129213073023894348858517586720482446642819095092562375940) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 146 = 11 +
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
    rw [show 39 = 28 +
      11 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_145_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_145_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_146_prefix_zero :
    (∑ x ∈ Finset.range 12,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (146 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (146 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_146_suffix_zero :
    (∑ x ∈ Finset.range 12,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (146 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_146 :
    recurrence2LeadingSquare.coeff 146 =
      -(((774808611791 * 10 ^ 70 +
        1400061978681725633010584534741957188038533809761026786215722729856771) * 10 ^ 70 +
        6644980729176630721819064282424621461093659529089084128927557856591460) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 147 = 12 +
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
    rw [show 39 = 27 +
      12 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_146_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_146_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_147_prefix_zero :
    (∑ x ∈ Finset.range 13,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (147 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (147 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_147_suffix_zero :
    (∑ x ∈ Finset.range 13,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (147 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_147 :
    recurrence2LeadingSquare.coeff 147 =
      (((1474787002410 * 10 ^ 70 +
        6372141496634960211141421921448609751302027119427342315804677288664001) * 10 ^ 70 +
        8260390615905870445831248501843141642749154276027059874903362776491762) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 148 = 13 +
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
    rw [show 39 = 26 +
      13 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_147_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_147_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_148_prefix_zero :
    (∑ x ∈ Finset.range 14,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (148 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (148 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_148_suffix_zero :
    (∑ x ∈ Finset.range 14,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (148 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_148 :
    recurrence2LeadingSquare.coeff 148 =
      -(((1680899995858 * 10 ^ 70 +
        1183219590352725847962921900759382545374071679525590875062757812356931) * 10 ^ 70 +
        5663146268865874482641583156592039313815314546398006877840262174624803) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 149 = 14 +
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
    rw [show 39 = 25 +
      14 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_148_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_148_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_149_prefix_zero :
    (∑ x ∈ Finset.range 15,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (149 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (149 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_149_suffix_zero :
    (∑ x ∈ Finset.range 15,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (149 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_149 :
    recurrence2LeadingSquare.coeff 149 =
      -(((1585107786913 * 10 ^ 70 +
        5550653012737987363500830326285951538596939471403320568102016159033243) * 10 ^ 70 +
        3148812983325335498117729879801095408148339201654025793702354158501974) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 150 = 15 +
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
    rw [show 39 = 24 +
      15 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_149_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_149_suffix_zero]
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_186_prefix_zero :
    (∑ x ∈ Finset.range 52,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (186 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (186 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_186_suffix_zero :
    (∑ x ∈ Finset.range 52,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (186 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_186 :
    recurrence2LeadingSquare.coeff 186 =
      (((14986326286332331 * 10 ^ 70 +
        0631279681426255074906526615336463964238914641187019181083037487667382) * 10 ^ 70 +
        8832225629771843700996964932489086562824051162992535348185468772858187) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 187 = 52 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 19 +
      52 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_186_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_186_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_187_prefix_zero :
    (∑ x ∈ Finset.range 53,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (187 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (187 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_187_suffix_zero :
    (∑ x ∈ Finset.range 53,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (187 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_187 :
    recurrence2LeadingSquare.coeff 187 =
      -(((9086361014156847 * 10 ^ 70 +
        4612558774044820166246472830895421199088711474789548739884042486558571) * 10 ^ 70 +
        0647876631820549867914579195473415220341145242861931901795741984714480) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 188 = 53 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 18 +
      53 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_187_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_187_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_188_prefix_zero :
    (∑ x ∈ Finset.range 54,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (188 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (188 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_188_suffix_zero :
    (∑ x ∈ Finset.range 54,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (188 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_188 :
    recurrence2LeadingSquare.coeff 188 =
      (((5325300239257643 * 10 ^ 70 +
        6572794702575718877739916977957379379017228347808751587521975140359994) * 10 ^ 70 +
        9674957397791616804949854615550682027266328477470158879162087945318790) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 189 = 54 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 17 +
      54 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_188_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_188_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_189_prefix_zero :
    (∑ x ∈ Finset.range 55,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (189 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (189 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_189_suffix_zero :
    (∑ x ∈ Finset.range 55,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (189 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_189 :
    recurrence2LeadingSquare.coeff 189 =
      -(((3016279426461505 * 10 ^ 70 +
        9508316015228691542643589080621716724803562123980904823154743481219857) * 10 ^ 70 +
        2452415880586974778130436970932241836845809801538663858549432499267406) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 190 = 55 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 16 +
      55 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_189_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_189_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_190_prefix_zero :
    (∑ x ∈ Finset.range 56,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (190 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (190 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_190_suffix_zero :
    (∑ x ∈ Finset.range 56,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (190 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_190 :
    recurrence2LeadingSquare.coeff 190 =
      (((1650727842166910 * 10 ^ 70 +
        3845145030097437167150021909350249052440435971368616619513570967403259) * 10 ^ 70 +
        3695375507379360429118235933898536861037633968562447432363988767503992) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 191 = 56 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 15 +
      56 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_190_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_190_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_191_prefix_zero :
    (∑ x ∈ Finset.range 57,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (191 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (191 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_191_suffix_zero :
    (∑ x ∈ Finset.range 57,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (191 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_191 :
    recurrence2LeadingSquare.coeff 191 =
      -(((872665400115388 * 10 ^ 70 +
        6669800089026371181771669032954299369563587312848426289737354612537640) * 10 ^ 70 +
        5883723961435713960648808540216494317078315824790638027378397359462466) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 192 = 57 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 14 +
      57 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_191_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_191_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_192_prefix_zero :
    (∑ x ∈ Finset.range 58,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (192 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (192 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_192_suffix_zero :
    (∑ x ∈ Finset.range 58,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (192 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_192 :
    recurrence2LeadingSquare.coeff 192 =
      (((445521889451028 * 10 ^ 70 +
        6680109398632045069138220363851799485026173579450137256020703886055717) * 10 ^ 70 +
        2298340233518511695792536550785799710290951658115055586594240498396410) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 193 = 58 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 13 +
      58 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_192_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_192_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_193_prefix_zero :
    (∑ x ∈ Finset.range 59,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (193 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (193 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_193_suffix_zero :
    (∑ x ∈ Finset.range 59,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (193 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_193 :
    recurrence2LeadingSquare.coeff 193 =
      -(((219587905799455 * 10 ^ 70 +
        3014549859593331837687112159164931765083060043798731919980140510940314) * 10 ^ 70 +
        0643635380512090967347525180696154548718630735778459441897371430380714) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 194 = 59 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 12 +
      59 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_193_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_193_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_194_prefix_zero :
    (∑ x ∈ Finset.range 60,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (194 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (194 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_194_suffix_zero :
    (∑ x ∈ Finset.range 60,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (194 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_194 :
    recurrence2LeadingSquare.coeff 194 =
      (((104453518178048 * 10 ^ 70 +
        1641076070905689763142264709859359042337636027258496416605222639770336) * 10 ^ 70 +
        5935110642028306029355654863583772074884198542912747826188495318744048) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 195 = 60 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 11 +
      60 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_194_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_194_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_195_prefix_zero :
    (∑ x ∈ Finset.range 61,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (195 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (195 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_195_suffix_zero :
    (∑ x ∈ Finset.range 61,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (195 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_195 :
    recurrence2LeadingSquare.coeff 195 =
      -(((47935579782235 * 10 ^ 70 +
        8464633089170019625824545374157962889873901278738697698800134471868296) * 10 ^ 70 +
        5140723207011661275201910127942609552300079045574211202028809728240362) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 196 = 61 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 10 +
      61 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_195_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_195_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_196_prefix_zero :
    (∑ x ∈ Finset.range 62,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (196 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (196 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_196_suffix_zero :
    (∑ x ∈ Finset.range 62,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (196 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_196 :
    recurrence2LeadingSquare.coeff 196 =
      (((21215118566463 * 10 ^ 70 +
        6501680895004036664187644129151859538880156853699149105150570395209905) * 10 ^ 70 +
        3280439890814794551283717636380388994588722905451525664835898869853258) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 197 = 62 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 9 +
      62 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_196_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_196_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_197_prefix_zero :
    (∑ x ∈ Finset.range 63,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (197 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (197 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_197_suffix_zero :
    (∑ x ∈ Finset.range 63,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (197 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_197 :
    recurrence2LeadingSquare.coeff 197 =
      -(((9051168786240 * 10 ^ 70 +
        5441439836983832360482295106660435751555146757662186934177190966125019) * 10 ^ 70 +
        8492542149933135131833808068093519969570845289951547007102929934644182) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 198 = 63 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 8 +
      63 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_197_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_197_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_198_prefix_zero :
    (∑ x ∈ Finset.range 64,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (198 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (198 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_198_suffix_zero :
    (∑ x ∈ Finset.range 64,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (198 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_198 :
    recurrence2LeadingSquare.coeff 198 =
      (((3720840246687 * 10 ^ 70 +
        0857812984779513470144544952763249975296051278865797461433460084201080) * 10 ^ 70 +
        5772753208889227399079341345395535569582083351646129789833621462910992) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 199 = 64 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 7 +
      64 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_198_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_198_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_199_prefix_zero :
    (∑ x ∈ Finset.range 65,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (199 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (199 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_199_suffix_zero :
    (∑ x ∈ Finset.range 65,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (199 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_199 :
    recurrence2LeadingSquare.coeff 199 =
      -(((1473145455882 * 10 ^ 70 +
        5732964456683428014716316899833585333561427081455722076914286343495309) * 10 ^ 70 +
        6366737700969443863546567619398711289077769995511331989764582488517850) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 200 = 65 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 6 +
      65 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_199_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_199_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_200_prefix_zero :
    (∑ x ∈ Finset.range 66,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (200 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (200 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_200_suffix_zero :
    (∑ x ∈ Finset.range 66,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (200 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_200 :
    recurrence2LeadingSquare.coeff 200 =
      (((561428560264 * 10 ^ 70 +
        2199486712935382136686481949688640833467451110536828033334862089416534) * 10 ^ 70 +
        7046015299533944586564123955397143595573777024387052958866133874303433) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 201 = 66 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 5 +
      66 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_200_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_200_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_201_prefix_zero :
    (∑ x ∈ Finset.range 67,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (201 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (201 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_201_suffix_zero :
    (∑ x ∈ Finset.range 67,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (201 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_201 :
    recurrence2LeadingSquare.coeff 201 =
      -(((205848539228 * 10 ^ 70 +
        9652587582171505717356442998855814379995469212146001916297531533077403) * 10 ^ 70 +
        3689306896662532594772338789476166084284604442088645764287103700196786) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 202 = 67 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 4 +
      67 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_201_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_201_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_202_prefix_zero :
    (∑ x ∈ Finset.range 68,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (202 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (202 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_202_suffix_zero :
    (∑ x ∈ Finset.range 68,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (202 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_202 :
    recurrence2LeadingSquare.coeff 202 =
      (((72568623252 * 10 ^ 70 +
        1959286265017552628139329746503025508086333319548343478076293197190786) * 10 ^ 70 +
        4849192694450337361582410533320162821089593098945664717628471582291894) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 203 = 68 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 3 +
      68 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_202_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_202_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_203_prefix_zero :
    (∑ x ∈ Finset.range 69,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (203 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (203 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_203_suffix_zero :
    (∑ x ∈ Finset.range 69,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (203 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_203 :
    recurrence2LeadingSquare.coeff 203 =
      -(((24582351115 * 10 ^ 70 +
        8519644431953424158709891013715060342333813834974847798802938764880273) * 10 ^ 70 +
        9737116107681517212486316386892706973745856382598405221150097407987948) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 204 = 69 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 2 +
      69 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_203_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_203_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_204_prefix_zero :
    (∑ x ∈ Finset.range 70,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (204 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (204 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_204_suffix_zero :
    (∑ x ∈ Finset.range 70,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (204 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_204 :
    recurrence2LeadingSquare.coeff 204 =
      (((7996098874 * 10 ^ 70 +
        2698794206824101326767543205209985161048450464971649753312748770740521) * 10 ^ 70 +
        2649576412150990483685128176926485723464700542073288009491805358354276) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 205 = 70 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 1 +
      70 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_204_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_204_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_205_prefix_zero :
    (∑ x ∈ Finset.range 71,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (205 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (205 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_205_suffix_zero :
    (∑ x ∈ Finset.range 71,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (205 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_205 :
    recurrence2LeadingSquare.coeff 205 =
      -(((2495742425 * 10 ^ 70 +
        0073540608005033702144520493004198829511714306579665628134413366408714) * 10 ^ 70 +
        2594869539507100191072451748192511992946078781798408185907761169961926) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 206 = 71 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_205_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_205_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_206_prefix_zero :
    (∑ x ∈ Finset.range 72,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (206 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (206 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_206_suffix_zero :
    (∑ x ∈ Finset.range 72,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (206 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_206 :
    recurrence2LeadingSquare.coeff 206 =
      (((746884458 * 10 ^ 70 +
        8194510803614343993663735046687399371702827044229828191466264116510209) * 10 ^ 70 +
        5543568330439761253337831837084810374781260574411589082665666690192664) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 207 = 72 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 31 +
      72 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_206_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_206_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_207_prefix_zero :
    (∑ x ∈ Finset.range 73,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (207 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (207 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_207_suffix_zero :
    (∑ x ∈ Finset.range 73,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (207 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_207 :
    recurrence2LeadingSquare.coeff 207 =
      -(((214131875 * 10 ^ 70 +
        4025057935649769128549900459379839011360884215641085923841322563838903) * 10 ^ 70 +
        0745391505051610551971271796890893598192436307375805611284795952813018) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 208 = 73 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 30 +
      73 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_207_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_207_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_208_prefix_zero :
    (∑ x ∈ Finset.range 74,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (208 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (208 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_208_suffix_zero :
    (∑ x ∈ Finset.range 74,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (208 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_208 :
    recurrence2LeadingSquare.coeff 208 =
      (((58762589 * 10 ^ 70 +
        7212314018797570118160340767157235051415403775782948668896135013564107) * 10 ^ 70 +
        3175823372477438550714180002583413058434039418091119505399717841591923) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 209 = 74 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 29 +
      74 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_208_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_208_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_209_prefix_zero :
    (∑ x ∈ Finset.range 75,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (209 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (209 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_209_suffix_zero :
    (∑ x ∈ Finset.range 75,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (209 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_209 :
    recurrence2LeadingSquare.coeff 209 =
      -(((15420665 * 10 ^ 70 +
        0640106433657232598524760722642144951740781624881186615666763952325571) * 10 ^ 70 +
        3255984462006274586688686844321424659629668605539152931890290413146682) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 210 = 75 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 28 +
      75 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_209_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_209_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_210_prefix_zero :
    (∑ x ∈ Finset.range 76,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (210 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (210 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_210_suffix_zero :
    (∑ x ∈ Finset.range 76,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (210 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_210 :
    recurrence2LeadingSquare.coeff 210 =
      (((3865894 * 10 ^ 70 +
        3510643320721691511950739758647762353420569909482153648533762933981736) * 10 ^ 70 +
        5696967650994421620507575863535867137046349149441829866460547304856617) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 211 = 76 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 27 +
      76 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_210_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_210_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_211_prefix_zero :
    (∑ x ∈ Finset.range 77,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (211 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (211 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_211_suffix_zero :
    (∑ x ∈ Finset.range 77,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (211 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_211 :
    recurrence2LeadingSquare.coeff 211 =
      -(((924852 * 10 ^ 70 +
        7261238256021057555322536937197390275022375730025557583937814968921061) * 10 ^ 70 +
        5384962400575975482322893615566211998335810900439317381147967402691502) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 212 = 77 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 26 +
      77 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_211_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_211_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_212_prefix_zero :
    (∑ x ∈ Finset.range 78,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (212 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (212 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_212_suffix_zero :
    (∑ x ∈ Finset.range 78,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (212 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_212 :
    recurrence2LeadingSquare.coeff 212 =
      (((210895 * 10 ^ 70 +
        9120186083789091118940517305552758272955768443611285127580236379241534) * 10 ^ 70 +
        7991413798311010318219073576195167170748698999809401650262622677560044) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 213 = 78 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 25 +
      78 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_212_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_212_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_213_prefix_zero :
    (∑ x ∈ Finset.range 79,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (213 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (213 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_213_suffix_zero :
    (∑ x ∈ Finset.range 79,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (213 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_213 :
    recurrence2LeadingSquare.coeff 213 =
      -(((45782 * 10 ^ 70 +
        2601972824516206469598138933949775236344718993676571710954164698310379) * 10 ^ 70 +
        9379628846607076060831217172084084707365169364635283034708100428074604) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 214 = 79 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 24 +
      79 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_213_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_213_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_214_prefix_zero :
    (∑ x ∈ Finset.range 80,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (214 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (214 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_214_suffix_zero :
    (∑ x ∈ Finset.range 80,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (214 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_214 :
    recurrence2LeadingSquare.coeff 214 =
      (((9448 * 10 ^ 70 +
        8766746509889255849292812731063315576284207458915266679624348279785212) * 10 ^ 70 +
        9885635069649933498809517369040691188310611150235513854717606586946080) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 215 = 80 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 23 +
      80 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_214_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_214_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_215_prefix_zero :
    (∑ x ∈ Finset.range 81,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (215 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (215 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_215_suffix_zero :
    (∑ x ∈ Finset.range 81,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (215 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_215 :
    recurrence2LeadingSquare.coeff 215 =
      -(((1851 * 10 ^ 70 +
        3712405206963375383080096680073657699445001432595742241329934295150539) * 10 ^ 70 +
        1934748106406742675555282122996678406973347414708674645145535459138784) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 216 = 81 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 22 +
      81 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_215_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_215_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_216_prefix_zero :
    (∑ x ∈ Finset.range 82,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (216 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (216 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_216_suffix_zero :
    (∑ x ∈ Finset.range 82,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (216 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_216 :
    recurrence2LeadingSquare.coeff 216 =
      (((343 * 10 ^ 70 +
        8472388040612105850856754691022873502849000507772554672767908631479709) * 10 ^ 70 +
        9898770156434235785534309517006124305592756228696766550809948904680295) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 217 = 82 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 21 +
      82 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_216_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_216_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_217_prefix_zero :
    (∑ x ∈ Finset.range 83,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (217 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (217 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_217_suffix_zero :
    (∑ x ∈ Finset.range 83,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (217 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_217 :
    recurrence2LeadingSquare.coeff 217 =
      -(((60 * 10 ^ 70 +
        4326362964279892456809182232038787418891779410127871892941479235512197) * 10 ^ 70 +
        0772942043900287562772000555670988096394051436231723001194728211388638) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 218 = 83 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 20 +
      83 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_217_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_217_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_218_prefix_zero :
    (∑ x ∈ Finset.range 84,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (218 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (218 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_218_suffix_zero :
    (∑ x ∈ Finset.range 84,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (218 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_218 :
    recurrence2LeadingSquare.coeff 218 =
      (((10 * 10 ^ 70 +
        0329401684757488517464079534304537745347867847229354044757424078856197) * 10 ^ 70 +
        1648307642529484751939942341821424879546494140473879702747914266619247) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 219 = 84 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 19 +
      84 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_218_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_218_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_219_prefix_zero :
    (∑ x ∈ Finset.range 85,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (219 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (219 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_219_suffix_zero :
    (∑ x ∈ Finset.range 85,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (219 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_219 :
    recurrence2LeadingSquare.coeff 219 =
      -(((1 * 10 ^ 70 +
        5703173748220766233378572841685589249080770261927797590607074742264867) * 10 ^ 70 +
        7192523641910750664469181180040774895962677542497325266128285532172158) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 220 = 85 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 18 +
      85 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_219_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_219_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_220_prefix_zero :
    (∑ x ∈ Finset.range 86,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (220 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (220 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_220_suffix_zero :
    (∑ x ∈ Finset.range 86,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (220 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_220 :
    recurrence2LeadingSquare.coeff 220 =
      ((2312218935472285628842558733467792252174177528659053760300299711174956 * 10 ^ 70 +
        9163287838227158023630917178970253568222818022541897891482908316945340) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 221 = 86 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 17 +
      86 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_220_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_220_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_221_prefix_zero :
    (∑ x ∈ Finset.range 87,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (221 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (221 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_221_suffix_zero :
    (∑ x ∈ Finset.range 87,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (221 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_221 :
    recurrence2LeadingSquare.coeff 221 =
      -((319559832823945006546574583572961229842470370677542546198353774389343 * 10 ^ 70 +
        2448652029500540205230659306111361871020509528326983259538586792558250) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 222 = 87 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 16 +
      87 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_221_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_221_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_222_prefix_zero :
    (∑ x ∈ Finset.range 88,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (222 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (222 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_222_suffix_zero :
    (∑ x ∈ Finset.range 88,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (222 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_222 :
    recurrence2LeadingSquare.coeff 222 =
      ((41349153610091287593392011456400566053374994798446085313984702078098 * 10 ^ 70 +
        3956975668630826749458332048498449562205561993888997379602102055512651) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 223 = 88 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 15 +
      88 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_222_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_222_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_223_prefix_zero :
    (∑ x ∈ Finset.range 89,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (223 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (223 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_223_suffix_zero :
    (∑ x ∈ Finset.range 89,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (223 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_223 :
    recurrence2LeadingSquare.coeff 223 =
      -((4995520856907125088556496549434134919611082967251503792589107608111 * 10 ^ 70 +
        0777521238124197583064949279349445676893514361490511486377601614426174) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 224 = 89 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 14 +
      89 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_223_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_223_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
