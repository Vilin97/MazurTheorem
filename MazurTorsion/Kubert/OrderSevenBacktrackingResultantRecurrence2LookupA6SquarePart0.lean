/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupA6
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupA6SquarePart0Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: A6Square coefficient convolution

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
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

theorem recurrence2A6Square_coeff_0 :
    recurrence2A6Square.coeff 0 =
      (367236 : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_1 :
    recurrence2A6Square.coeff 1 =
      (320433408 : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_2 :
    recurrence2A6Square.coeff 2 =
      (-726225892224 : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_3 :
    recurrence2A6Square.coeff 3 =
      (-294474723824064 : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_4 :
    recurrence2A6Square.coeff 4 =
      (464120236252019788 : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_5 :
    recurrence2A6Square.coeff 5 =
      (-53400331900197746408 : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_6 :
    recurrence2A6Square.coeff 6 =
      (-8633722375944673064456 : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_7 :
    recurrence2A6Square.coeff 7 =
      (992819644042940170542112 : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_8 :
    recurrence2A6Square.coeff 8 =
      (65245796628267972775130425 : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_9 :
    recurrence2A6Square.coeff 9 =
      (-5387724804960970325367574620 : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_10 :
    recurrence2A6Square.coeff 10 =
      (-239752130710663437082465609304 : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_11 :
    recurrence2A6Square.coeff 11 =
      (10591831325297987850209667674488 : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_12 :
    recurrence2A6Square.coeff 12 =
      (543306677502943330905967625539148 : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_13 :
    recurrence2A6Square.coeff 13 =
      (-7644570321992671118344849536041432 : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_14 :
    recurrence2A6Square.coeff 14 =
      (-663107204115896673573158804269558860 : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_15 :
    recurrence2A6Square.coeff 15 =
      (-1918050890550064194508188905236858892 : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_16 :
    recurrence2A6Square.coeff 16 =
      (429686380107142306691559871531608112384 : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_17 :
    recurrence2A6Square.coeff 17 =
      (6188816923714238478801695732458426662892 : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_18 :
    recurrence2A6Square.coeff 18 =
      (-133266518951075155572580548772871240713606 : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_19 :
    recurrence2A6Square.coeff 19 =
      (-3965943302423021476252402578495916814569166 : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_20 :
    recurrence2A6Square.coeff 20 =
      (6395857762157684706034945697294275289788108 : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_21 :
    recurrence2A6Square.coeff 21 =
      (1247529386423853141672331956164529632763194296 : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_22 :
    recurrence2A6Square.coeff 22 =
      (9583542587277504622829545991211860758980980520 : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_23 :
    recurrence2A6Square.coeff 23 =
      (-210182824908398529810730179450903606070664170454 : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_24 :
    recurrence2A6Square.coeff 24 =
      (-3560730146204407631272615156506513014423474036778 : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_25 :
    recurrence2A6Square.coeff 25 =
      (12110762630579958486589442009998540473379140723452 : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_26 :
    recurrence2A6Square.coeff 26 =
      (665963770877128425690484404446501965208823486462914 : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_27 :
    recurrence2A6Square.coeff 27 =
      (2335071183799749936873553855538821363805294657753480 : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_28 :
    recurrence2A6Square.coeff 28 =
      (-74434669568937775819295549628806039497643425155891239 : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_29 :
    recurrence2A6Square.coeff 29 =
      (-685894859189690671732836519511981916339804837266289294 : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_30 :
    recurrence2A6Square.coeff 30 =
      (4832068368877478519556438186657188606136427646221955395 : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_31 :
    recurrence2A6Square.coeff 31 =
      (91157283346920700466994306302908034554960253564792117378 : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_32 :
    recurrence2A6Square.coeff 32 =
      (-59986423008138042839986185243383917612631713529272124240 : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_33 :
    recurrence2A6Square.coeff 33 =
      (-8058603794116714402807493550302845781599104026510270482608 : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_34 :
    recurrence2A6Square.coeff 34 =
      (-24132942466766875393006086049806486210094013904591473529364 : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_35 :
    recurrence2A6Square.coeff 35 =
      (512433073128603376975188739962730943378508431123751351659162 : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_36 :
    recurrence2A6Square.coeff 36 =
      (3207601224460504512110606281228111393878447422236284018839928 : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_37 :
    recurrence2A6Square.coeff 37 =
      (-23845482468872692342649436555924340106851613398764156787233482 : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_38 :
    recurrence2A6Square.coeff 38 =
      (-251554713250016723695828992103525483178121299806981464588545983 : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_39 :
    recurrence2A6Square.coeff 39 =
      (755326105462957901263970330927041508095352893464017362905137348 : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_40 :
    recurrence2A6Square.coeff 40 =
      (14772465744719064768616520639993425108155439707894295355290952981 : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_41 :
    recurrence2A6Square.coeff 41 =
      (-9650674502751096275934028521337850555956799211891892957643978006 : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_42 :
    recurrence2A6Square.coeff 42 =
      (-702920160719549557318053975916168726036005025170308582635051176562 : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_43 :
    recurrence2A6Square.coeff 43 =
      (-624312716048331776172126630734718420650028763405546048981383295758 : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_44 :
    recurrence2A6Square.coeff 44 =
      (28317808036172787754036709594998205929017083468535226987943247448095 : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_45 :
    recurrence2A6Square.coeff 45 =
      (56988448577948202268534037088360535478670923782424817290031827262728 : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_46 :
    recurrence2A6Square.coeff 46 =
      (-996200703078279744637343700106980121642174442009429884698170263197016 : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_47 :
    recurrence2A6Square.coeff 47 =
      (-2844873010192876370260117363577819043383997560683282266826795715169952 : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_48 :
    recurrence2A6Square.coeff 48 =
      ((3 * 10 ^ 70 +
        1393631612569444261285649534497245314777835820039241902308109368137430) : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_49 :
    recurrence2A6Square.coeff 49 =
      ((10 * 10 ^ 70 +
        8131333312190369115525025765663261758223108655664169955439484160075962) : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_50 :
    recurrence2A6Square.coeff 50 =
      -((90 * 10 ^ 70 +
        5673183208008440650901492073698661564667662737758115052007069388059988) : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_51 :
    recurrence2A6Square.coeff 51 =
      -((339 * 10 ^ 70 +
        8242081649818886643999341460034740108213987899023087230014928713811442) : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_52 :
    recurrence2A6Square.coeff 52 =
      ((2432 * 10 ^ 70 +
        9695481951815048158067610177492531427454291468916472734988771454914727) : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_53 :
    recurrence2A6Square.coeff 53 =
      ((9108 * 10 ^ 70 +
        0999791592583221711932083760390481404960932930181168969770036231977528) : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_54 :
    recurrence2A6Square.coeff 54 =
      -((61480 * 10 ^ 70 +
        6350128155987396717661923966318586513140695538134427896720876462301047) : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_55 :
    recurrence2A6Square.coeff 55 =
      -((210001 * 10 ^ 70 +
        9886463601891802915636924377558414142981615203493897101810384466413252) : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_56 :
    recurrence2A6Square.coeff 56 =
      ((1463778 * 10 ^ 70 +
        9736165510138191868035024108385806179874701928052736640765685115321132) : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_57 :
    recurrence2A6Square.coeff 57 =
      ((4125513 * 10 ^ 70 +
        1005903212626762456199748291482068214290496275150627431630108233861814) : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_58 :
    recurrence2A6Square.coeff 58 =
      -((32622358 * 10 ^ 70 +
        9083855691381203994963701948791522963921743235703580597496271533085089) : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_59 :
    recurrence2A6Square.coeff 59 =
      -((66467462 * 10 ^ 70 +
        9629373532422347489920582804439419113107151904785339196782832459472414) : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_60 :
    recurrence2A6Square.coeff 60 =
      ((672035071 * 10 ^ 70 +
        3769886277214938006179601400609240975483691105091418163619484030885488) : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_61 :
    recurrence2A6Square.coeff 61 =
      ((777096629 * 10 ^ 70 +
        8970990655910698493454772070643302166437803163264657715899512476574302) : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_62 :
    recurrence2A6Square.coeff 62 =
      -((12585064196 * 10 ^ 70 +
        5168527972620557613137213694060240866933348359612026799652443534507566) : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_63 :
    recurrence2A6Square.coeff 63 =
      -((2816191745 * 10 ^ 70 +
        8127805666829186937070763664878074884443598120098037350710607194568586) : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_64 :
    recurrence2A6Square.coeff 64 =
      ((209839011573 * 10 ^ 70 +
        1753257719687047425334093381198082966460607476127550694358350672564041) : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_65 :
    recurrence2A6Square.coeff 65 =
      -((160076190735 * 10 ^ 70 +
        4883621558337888095225627749189661135881065959898475440266862734433588) : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_66 :
    recurrence2A6Square.coeff 66 =
      -((3027732392670 * 10 ^ 70 +
        9594875357790099416287478891815031627969418553550858470037248671814012) : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_67 :
    recurrence2A6Square.coeff 67 =
      ((5690657002878 * 10 ^ 70 +
        2038321263121776157539678392532161328491930305043676051021240031646394) : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_68 :
    recurrence2A6Square.coeff 68 =
      ((36018065322891 * 10 ^ 70 +
        9707880304689094105111296129103601373005830892390415619991402163669634) : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_69 :
    recurrence2A6Square.coeff 69 =
      -((121305107266090 * 10 ^ 70 +
        9545089687457970083028257398155142643362566342415790796479109582096300) : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_70 :
    recurrence2A6Square.coeff 70 =
      -((314575187529291 * 10 ^ 70 +
        5743292387837293642356445126543083610269151387599797251142923537598633) : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_71 :
    recurrence2A6Square.coeff 71 =
      ((1945093505194447 * 10 ^ 70 +
        8975151806111022093978919533006603951662773130527920585154925501781294) : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_72 :
    recurrence2A6Square.coeff 72 =
      ((1104700562978846 * 10 ^ 70 +
        2397728644367191747568192934347382210007860739304841488694620935808037) : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_73 :
    recurrence2A6Square.coeff 73 =
      -((24265363836252101 * 10 ^ 70 +
        0932547188946368602143320171281857414246201753722238685588717948415532) : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_74 :
    recurrence2A6Square.coeff 74 =
      ((23714648159869481 * 10 ^ 70 +
        9365713375999191917530676883742276250001965856077966793738610212044312) : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_75 :
    recurrence2A6Square.coeff 75 =
      ((226110394519448357 * 10 ^ 70 +
        8544910290434290793701738371777087868125182533809387720444766193262998) : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_76 :
    recurrence2A6Square.coeff 76 =
      -((604479607139251898 * 10 ^ 70 +
        0555562136842240298457826747811099650149536690617830587775290928638261) : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_77 :
    recurrence2A6Square.coeff 77 =
      -((1289673020206788752 * 10 ^ 70 +
        6695214062631599686764791030614096610554999046211817478241445148468992) : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_78 :
    recurrence2A6Square.coeff 78 =
      ((7996695445499739315 * 10 ^ 70 +
        7331237789955793055442103050091549695781906748621924913988107646080678) : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_79 :
    recurrence2A6Square.coeff 79 =
      -((1604463549547243783 * 10 ^ 70 +
        7366026981038755437334848561060339009721488797040411150979109193340956) : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_80 :
    recurrence2A6Square.coeff 80 =
      -((69049275299115167547 * 10 ^ 70 +
        7953275619889982299085411345258331858126224826353317365745055369554778) : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_81 :
    recurrence2A6Square.coeff 81 =
      ((136734049863501668766 * 10 ^ 70 +
        3501675183130457359830179654057168437539765514097273301461278922830552) : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_82 :
    recurrence2A6Square.coeff 82 =
      ((327751050717585784010 * 10 ^ 70 +
        4088053527838654329092800093173465916912233318596612556240675293271565) : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_83 :
    recurrence2A6Square.coeff 83 =
      -((1703791362083630682531 * 10 ^ 70 +
        3003203853868738002632373270111296079941321212531011190367470552064088) : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_84 :
    recurrence2A6Square.coeff 84 =
      ((666487772129239827222 * 10 ^ 70 +
        7301469290347937913476932570685089875356719682044865231008023206591493) : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_85 :
    recurrence2A6Square.coeff 85 =
      ((11418493131211855239955 * 10 ^ 70 +
        2391949341902945632764502638026976918108017564613376602449451636324280) : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_86 :
    recurrence2A6Square.coeff 86 =
      -((26913241158857686912371 * 10 ^ 70 +
        3162213574802647737571598053013434649539539408954215959479983514163284) : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_87 :
    recurrence2A6Square.coeff 87 =
      -((25897867580774925216042 * 10 ^ 70 +
        6598495118241645916530942823114959069239666821058922574638662287376512) : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_88 :
    recurrence2A6Square.coeff 88 =
      ((230274886565412946667335 * 10 ^ 70 +
        9889022671388911536692408535376662585509589036831269682753699585068353) : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_89 :
    recurrence2A6Square.coeff 89 =
      -((298798017769598932023463 * 10 ^ 70 +
        4746850143629854707966058095726155650743949646800219781216333068582106) : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_90 :
    recurrence2A6Square.coeff 90 =
      -((804643725455500590834144 * 10 ^ 70 +
        7791963670108931627122621561275755946299799419495205012393964435906996) : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_91 :
    recurrence2A6Square.coeff 91 =
      ((3420011932192273250226476 * 10 ^ 70 +
        3017336253599750209868583224949224819177957993777692577433266237954128) : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_92 :
    recurrence2A6Square.coeff 92 =
      -((2551368155750412746357830 * 10 ^ 70 +
        0704405569383294964894910983500493055741012906076284286015153589470490) : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_93 :
    recurrence2A6Square.coeff 93 =
      -((13250920180049005781054293 * 10 ^ 70 +
        6477079748517589335974656411479207951263124297499429094542853276213906) : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_94 :
    recurrence2A6Square.coeff 94 =
      ((41312573896267259929035941 * 10 ^ 70 +
        3714372369609718857116862920188000541701778146419310406400175916875364) : ℚ) := by
  unfold recurrence2A6Square
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

theorem recurrence2A6Square_coeff_95 :
    recurrence2A6Square.coeff 95 =
      -((21622133814079042767500475 * 10 ^ 70 +
        7248301036970873862295250296658675163051859320718618600511858518353278) : ℚ) := by
  unfold recurrence2A6Square
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

private theorem recurrence2A6Square_coeff_96_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (96 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_96_suffix_zero :
    (∑ x ∈ Finset.range 1,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (96 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_96 :
    recurrence2A6Square.coeff 96 =
      -((151626127792015900082818480 * 10 ^ 70 +
        9138904365686605181639081833896409519704319070905036672816514031458437) : ℚ) := by
  unfold recurrence2A6Square
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
    rw [show 32 = 31 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_96_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_96_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_97_prefix_zero :
    (∑ x ∈ Finset.range 2,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (97 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (97 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_97_suffix_zero :
    (∑ x ∈ Finset.range 2,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (97 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_97 :
    recurrence2A6Square.coeff 97 =
      ((425210177873904491075668044 * 10 ^ 70 +
        4553471287891925185052267382102308894082740570672331873205936018828872) : ℚ) := by
  unfold recurrence2A6Square
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
    rw [show 32 = 30 +
      2 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_97_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_97_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_98_prefix_zero :
    (∑ x ∈ Finset.range 3,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (98 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (98 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_98_suffix_zero :
    (∑ x ∈ Finset.range 3,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (98 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_98 :
    recurrence2A6Square.coeff 98 =
      -((253614798739166917663588319 * 10 ^ 70 +
        6559868429602758411249360742869236516885363025379031972855322209283580) : ℚ) := by
  unfold recurrence2A6Square
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
    rw [show 32 = 29 +
      3 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_98_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_98_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_99_prefix_zero :
    (∑ x ∈ Finset.range 4,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (99 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (99 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_99_suffix_zero :
    (∑ x ∈ Finset.range 4,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (99 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_99 :
    recurrence2A6Square.coeff 99 =
      -((1230236655730225641554612088 * 10 ^ 70 +
        1615890793097754096297260471556207942617768026295290848035631065383180) : ℚ) := by
  unfold recurrence2A6Square
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
    rw [show 32 = 28 +
      4 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_99_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_99_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_100_prefix_zero :
    (∑ x ∈ Finset.range 5,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (100 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (100 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_100_suffix_zero :
    (∑ x ∈ Finset.range 5,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (100 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_100 :
    recurrence2A6Square.coeff 100 =
      ((3681131926240919712818319196 * 10 ^ 70 +
        5056427190706403798609542086131180238001569663118151047177362974974720) : ℚ) := by
  unfold recurrence2A6Square
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
    rw [show 32 = 27 +
      5 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_100_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_100_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_101_prefix_zero :
    (∑ x ∈ Finset.range 6,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (101 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (101 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_101_suffix_zero :
    (∑ x ∈ Finset.range 6,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (101 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_101 :
    recurrence2A6Square.coeff 101 =
      -((3314643252565882828462229425 * 10 ^ 70 +
        0675099836073592405589176291265229836995454160320444134939127427248682) : ℚ) := by
  unfold recurrence2A6Square
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
    rw [show 32 = 26 +
      6 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_101_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_101_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_102_prefix_zero :
    (∑ x ∈ Finset.range 7,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (102 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (102 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_102_suffix_zero :
    (∑ x ∈ Finset.range 7,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (102 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_102 :
    recurrence2A6Square.coeff 102 =
      -((6115137209324684237326899320 * 10 ^ 70 +
        7432665957827626141283142804950242038594137841140247473841115538425286) : ℚ) := by
  unfold recurrence2A6Square
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
    rw [show 32 = 25 +
      7 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_102_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_102_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_103_prefix_zero :
    (∑ x ∈ Finset.range 8,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (103 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (103 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_103_suffix_zero :
    (∑ x ∈ Finset.range 8,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (103 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_103 :
    recurrence2A6Square.coeff 103 =
      ((24613095300705460465799416609 * 10 ^ 70 +
        7531696566465805960628298420354151750549557055890935183815220569001842) : ℚ) := by
  unfold recurrence2A6Square
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
    rw [show 32 = 24 +
      8 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_103_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_103_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_104_prefix_zero :
    (∑ x ∈ Finset.range 9,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (104 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (104 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_104_suffix_zero :
    (∑ x ∈ Finset.range 9,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (104 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_104 :
    recurrence2A6Square.coeff 104 =
      -((33220640249495279934154582544 * 10 ^ 70 +
        1834790776387693924378227383877131955171350701292446756067286426027806) : ℚ) := by
  unfold recurrence2A6Square
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
    rw [show 32 = 23 +
      9 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_104_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_104_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_105_prefix_zero :
    (∑ x ∈ Finset.range 10,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (105 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (105 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_105_suffix_zero :
    (∑ x ∈ Finset.range 10,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (105 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_105 :
    recurrence2A6Square.coeff 105 =
      -((4344063502825837543661983194 * 10 ^ 70 +
        2000616167451543425709470865624414757324319771961191147449140418367864) : ℚ) := by
  unfold recurrence2A6Square
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
    rw [show 32 = 22 +
      10 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_105_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_105_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_106_prefix_zero :
    (∑ x ∈ Finset.range 11,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (106 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (106 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_106_suffix_zero :
    (∑ x ∈ Finset.range 11,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (106 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_106 :
    recurrence2A6Square.coeff 106 =
      ((105519577620803740150510126688 * 10 ^ 70 +
        5427776588787648901934017340227248873035846026355674783258882751355370) : ℚ) := by
  unfold recurrence2A6Square
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
    rw [show 32 = 21 +
      11 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_106_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_106_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_107_prefix_zero :
    (∑ x ∈ Finset.range 12,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (107 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (107 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_107_suffix_zero :
    (∑ x ∈ Finset.range 12,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (107 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_107 :
    recurrence2A6Square.coeff 107 =
      -((210859980857905865514098839502 * 10 ^ 70 +
        9091440665716247416795986018211151144496089291837757697590355110084924) : ℚ) := by
  unfold recurrence2A6Square
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
    rw [show 32 = 20 +
      12 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_107_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_107_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_108_prefix_zero :
    (∑ x ∈ Finset.range 13,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (108 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (108 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_108_suffix_zero :
    (∑ x ∈ Finset.range 13,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (108 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_108 :
    recurrence2A6Square.coeff 108 =
      ((170129192611990706727503295372 * 10 ^ 70 +
        1226126320908191909867907717863103611196617966445354681730264150182443) : ℚ) := by
  unfold recurrence2A6Square
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
    rw [show 32 = 19 +
      13 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_108_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_108_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_109_prefix_zero :
    (∑ x ∈ Finset.range 14,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (109 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (109 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_109_suffix_zero :
    (∑ x ∈ Finset.range 14,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (109 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_109 :
    recurrence2A6Square.coeff 109 =
      ((153955143647337553962273310752 * 10 ^ 70 +
        4045655601192325646257784254115893975230873583326760169161814686234330) : ℚ) := by
  unfold recurrence2A6Square
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
    rw [show 32 = 18 +
      14 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_109_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_109_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_110_prefix_zero :
    (∑ x ∈ Finset.range 15,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (110 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (110 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_110_suffix_zero :
    (∑ x ∈ Finset.range 15,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (110 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_110 :
    recurrence2A6Square.coeff 110 =
      -((689330870059857573965041626065 * 10 ^ 70 +
        7115713606105270487408521592560241179555101591220025057032649026359269) : ℚ) := by
  unfold recurrence2A6Square
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
    rw [show 32 = 17 +
      15 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_110_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_110_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_111_prefix_zero :
    (∑ x ∈ Finset.range 16,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (111 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (111 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_111_suffix_zero :
    (∑ x ∈ Finset.range 16,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (111 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_111 :
    recurrence2A6Square.coeff 111 =
      ((1044296045066576024948639240739 * 10 ^ 70 +
        9181977858812555071991693734950593088891912562575016671384445282241476) : ℚ) := by
  unfold recurrence2A6Square
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
    rw [show 32 = 16 +
      16 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_111_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_111_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_112_prefix_zero :
    (∑ x ∈ Finset.range 17,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (112 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (112 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_112_suffix_zero :
    (∑ x ∈ Finset.range 17,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (112 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_112 :
    recurrence2A6Square.coeff 112 =
      -((693781247777736399266910692262 * 10 ^ 70 +
        2067047060586493932919236204353934642849348585122852325629107322241790) : ℚ) := by
  unfold recurrence2A6Square
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
    rw [show 32 = 15 +
      17 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_112_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_112_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_113_prefix_zero :
    (∑ x ∈ Finset.range 18,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (113 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (113 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_113_suffix_zero :
    (∑ x ∈ Finset.range 18,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (113 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_113 :
    recurrence2A6Square.coeff 113 =
      -((551510537906377065487063612955 * 10 ^ 70 +
        6857782938103055223787699200428300177157211747238506342283878065120204) : ℚ) := by
  unfold recurrence2A6Square
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
    rw [show 32 = 14 +
      18 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_113_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_113_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_114_prefix_zero :
    (∑ x ∈ Finset.range 19,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (114 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (114 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_114_suffix_zero :
    (∑ x ∈ Finset.range 19,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (114 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_114 :
    recurrence2A6Square.coeff 114 =
      ((2155066023591005776692670293825 * 10 ^ 70 +
        5244913556540826435178711231157568963785933213433260157380523990989381) : ℚ) := by
  unfold recurrence2A6Square
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
    rw [show 32 = 13 +
      19 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_114_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_114_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_115_prefix_zero :
    (∑ x ∈ Finset.range 20,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (115 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (115 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_115_suffix_zero :
    (∑ x ∈ Finset.range 20,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (115 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_115 :
    recurrence2A6Square.coeff 115 =
      -((3005690708370423736498070447305 * 10 ^ 70 +
        2591434849412351004359746179526605928198377735474657758113183855434674) : ℚ) := by
  unfold recurrence2A6Square
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
    rw [show 32 = 12 +
      20 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_115_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_115_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_116_prefix_zero :
    (∑ x ∈ Finset.range 21,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (116 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (116 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_116_suffix_zero :
    (∑ x ∈ Finset.range 21,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (116 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_116 :
    recurrence2A6Square.coeff 116 =
      ((2183889253535235341564722652205 * 10 ^ 70 +
        4344443853287901822320276396437363678085413402338523056986728996293831) : ℚ) := by
  unfold recurrence2A6Square
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
    rw [show 32 = 11 +
      21 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_116_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_116_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_117_prefix_zero :
    (∑ x ∈ Finset.range 22,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (117 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (117 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_117_suffix_zero :
    (∑ x ∈ Finset.range 22,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (117 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_117 :
    recurrence2A6Square.coeff 117 =
      ((199775645227486015813275196085 * 10 ^ 70 +
        3614958008400323003806404601063026913498409837918523081610966039125748) : ℚ) := by
  unfold recurrence2A6Square
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
    rw [show 32 = 10 +
      22 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_117_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_117_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_118_prefix_zero :
    (∑ x ∈ Finset.range 23,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (118 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (118 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_118_suffix_zero :
    (∑ x ∈ Finset.range 23,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (118 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_118 :
    recurrence2A6Square.coeff 118 =
      -((2864515169981647206484011943035 * 10 ^ 70 +
        2346599076890300380605767702183852126396789748891554969630028511221807) : ℚ) := by
  unfold recurrence2A6Square
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
    rw [show 32 = 9 +
      23 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_118_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_118_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_119_prefix_zero :
    (∑ x ∈ Finset.range 24,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (119 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (119 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_119_suffix_zero :
    (∑ x ∈ Finset.range 24,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (119 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_119 :
    recurrence2A6Square.coeff 119 =
      ((4177264740139359104192970056293 * 10 ^ 70 +
        5244081651117737378748265820974154261968813912977668069423360386948304) : ℚ) := by
  unfold recurrence2A6Square
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
    rw [show 32 = 8 +
      24 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_119_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_119_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_120_prefix_zero :
    (∑ x ∈ Finset.range 25,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (120 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (120 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_120_suffix_zero :
    (∑ x ∈ Finset.range 25,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (120 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_120 :
    recurrence2A6Square.coeff 120 =
      -((3334585383714148077094873266426 * 10 ^ 70 +
        6423542206278787059483850506238203256740781574314416512356192923255728) : ℚ) := by
  unfold recurrence2A6Square
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
    rw [show 32 = 7 +
      25 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_120_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_120_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_121_prefix_zero :
    (∑ x ∈ Finset.range 26,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (121 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (121 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_121_suffix_zero :
    (∑ x ∈ Finset.range 26,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (121 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_121 :
    recurrence2A6Square.coeff 121 =
      ((937986005793131564799993479166 * 10 ^ 70 +
        5269328269495548341459227680027864936640932933838113973467485827777696) : ℚ) := by
  unfold recurrence2A6Square
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
    rw [show 32 = 6 +
      26 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_121_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_121_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_122_prefix_zero :
    (∑ x ∈ Finset.range 27,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (122 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (122 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_122_suffix_zero :
    (∑ x ∈ Finset.range 27,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (122 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_122 :
    recurrence2A6Square.coeff 122 =
      ((1502071842839643655747258398417 * 10 ^ 70 +
        8916946805381922174071385505241265111430870605191470965739875058295966) : ℚ) := by
  unfold recurrence2A6Square
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
    rw [show 32 = 5 +
      27 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_122_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_122_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_123_prefix_zero :
    (∑ x ∈ Finset.range 28,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (123 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (123 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_123_suffix_zero :
    (∑ x ∈ Finset.range 28,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (123 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_123 :
    recurrence2A6Square.coeff 123 =
      -((2678509380044286629102161678798 * 10 ^ 70 +
        1133222537699528935223045978461079445464969871285577235274165624340068) : ℚ) := by
  unfold recurrence2A6Square
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
    rw [show 32 = 4 +
      28 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_123_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_123_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_124_prefix_zero :
    (∑ x ∈ Finset.range 29,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (124 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (124 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_124_suffix_zero :
    (∑ x ∈ Finset.range 29,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (124 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_124 :
    recurrence2A6Square.coeff 124 =
      ((2296071304123135711804378006248 * 10 ^ 70 +
        7221181595722309923348305544764668067030588888959633824710709744424747) : ℚ) := by
  unfold recurrence2A6Square
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
    rw [show 32 = 3 +
      29 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_124_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_124_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_125_prefix_zero :
    (∑ x ∈ Finset.range 30,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (125 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (125 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_125_suffix_zero :
    (∑ x ∈ Finset.range 30,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (125 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_125 :
    recurrence2A6Square.coeff 125 =
      -((1025784110219643742336797144505 * 10 ^ 70 +
        1886287261622417133720714775735396010823951665551510315818511923282236) : ℚ) := by
  unfold recurrence2A6Square
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
    rw [show 32 = 2 +
      30 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_125_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_125_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_126_prefix_zero :
    (∑ x ∈ Finset.range 31,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (126 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (126 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_126_suffix_zero :
    (∑ x ∈ Finset.range 31,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (126 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_126 :
    recurrence2A6Square.coeff 126 =
      -((177362120744645718613951552428 * 10 ^ 70 +
        7988857063391048845814889869616946176347516559664850936030686903245991) : ℚ) := by
  unfold recurrence2A6Square
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
    rw [show 32 = 1 +
      31 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_126_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_126_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_127_prefix_zero :
    (∑ x ∈ Finset.range 32,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (127 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (127 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_127_suffix_zero :
    (∑ x ∈ Finset.range 32,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (127 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_127 :
    recurrence2A6Square.coeff 127 =
      ((743143677945647005074163954492 * 10 ^ 70 +
        4124535233803378191168278723774079573713681993958551421401835877152602) : ℚ) := by
  unfold recurrence2A6Square
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
  rw [recurrence2A6Square_coeff_127_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_127_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_128_prefix_zero :
    (∑ x ∈ Finset.range 33,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (128 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (128 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_128_suffix_zero :
    (∑ x ∈ Finset.range 33,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (128 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_128 :
    recurrence2A6Square.coeff 128 =
      -((681339607686321075556062926504 * 10 ^ 70 +
        9563641766863307518028336817116163826788329663371256397667175996825766) : ℚ) := by
  unfold recurrence2A6Square
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
    rw [show 64 = 31 +
      33 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_128_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_128_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_129_prefix_zero :
    (∑ x ∈ Finset.range 34,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (129 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (129 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_129_suffix_zero :
    (∑ x ∈ Finset.range 34,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (129 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_129 :
    recurrence2A6Square.coeff 129 =
      ((335527263515948981900198182831 * 10 ^ 70 +
        7019960333754998878849759787503912007178520792006210609109866674482166) : ℚ) := by
  unfold recurrence2A6Square
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
    rw [show 64 = 30 +
      34 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_129_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_129_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_130_prefix_zero :
    (∑ x ∈ Finset.range 35,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (130 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (130 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_130_suffix_zero :
    (∑ x ∈ Finset.range 35,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (130 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_130 :
    recurrence2A6Square.coeff 130 =
      -((31999869725921005866303890692 * 10 ^ 70 +
        1864554745086183730831011229149159216186527310838267028875177696294705) : ℚ) := by
  unfold recurrence2A6Square
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
    rw [show 64 = 29 +
      35 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_130_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_130_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_131_prefix_zero :
    (∑ x ∈ Finset.range 36,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (131 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (131 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_131_suffix_zero :
    (∑ x ∈ Finset.range 36,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (131 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_131 :
    recurrence2A6Square.coeff 131 =
      -((99518347461694255634587295945 * 10 ^ 70 +
        7399584596076492727136114346578452142181980758671541564557546537076614) : ℚ) := by
  unfold recurrence2A6Square
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
    rw [show 64 = 28 +
      36 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_131_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_131_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_132_prefix_zero :
    (∑ x ∈ Finset.range 37,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (132 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (132 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_132_suffix_zero :
    (∑ x ∈ Finset.range 37,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (132 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_132 :
    recurrence2A6Square.coeff 132 =
      ((96023251852745477585953389866 * 10 ^ 70 +
        2806649718827263547784857456256951657344586351734202653957062967543208) : ℚ) := by
  unfold recurrence2A6Square
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
    rw [show 64 = 27 +
      37 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_132_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_132_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_133_prefix_zero :
    (∑ x ∈ Finset.range 38,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (133 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (133 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_133_suffix_zero :
    (∑ x ∈ Finset.range 38,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (133 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_133 :
    recurrence2A6Square.coeff 133 =
      -((45803108740913760451510283690 * 10 ^ 70 +
        8841582571142431975705917747593305993733178125028491267840601993525142) : ℚ) := by
  unfold recurrence2A6Square
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
    rw [show 64 = 26 +
      38 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_133_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_133_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_134_prefix_zero :
    (∑ x ∈ Finset.range 39,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (134 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (134 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_134_suffix_zero :
    (∑ x ∈ Finset.range 39,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (134 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_134 :
    recurrence2A6Square.coeff 134 =
      ((6969232844304159881242516689 * 10 ^ 70 +
        8715205400604770605018437670608903523554499738481834159396473997990875) : ℚ) := by
  unfold recurrence2A6Square
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
    rw [show 64 = 25 +
      39 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_134_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_134_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_135_prefix_zero :
    (∑ x ∈ Finset.range 40,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (135 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (135 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_135_suffix_zero :
    (∑ x ∈ Finset.range 40,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (135 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_135 :
    recurrence2A6Square.coeff 135 =
      ((7235270187952450752783289311 * 10 ^ 70 +
        8824352716447530164696275449880954855222365826886874798564808229140142) : ℚ) := by
  unfold recurrence2A6Square
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
    rw [show 64 = 24 +
      40 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_135_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_135_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_136_prefix_zero :
    (∑ x ∈ Finset.range 41,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (136 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (136 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_136_suffix_zero :
    (∑ x ∈ Finset.range 41,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (136 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_136 :
    recurrence2A6Square.coeff 136 =
      -((6684000336881809316080867280 * 10 ^ 70 +
        4501976298896608869711449503518093227901769038364615240752733956073954) : ℚ) := by
  unfold recurrence2A6Square
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
    rw [show 64 = 23 +
      41 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_136_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_136_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_137_prefix_zero :
    (∑ x ∈ Finset.range 42,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (137 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (137 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_137_suffix_zero :
    (∑ x ∈ Finset.range 42,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (137 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_137 :
    recurrence2A6Square.coeff 137 =
      ((2711291863175288662682829790 * 10 ^ 70 +
        2816789136955519958371179799429943510228894693114092624513100811800232) : ℚ) := by
  unfold recurrence2A6Square
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
    rw [show 64 = 22 +
      42 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_137_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_137_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_138_prefix_zero :
    (∑ x ∈ Finset.range 43,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (138 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (138 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_138_suffix_zero :
    (∑ x ∈ Finset.range 43,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (138 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_138 :
    recurrence2A6Square.coeff 138 =
      -((284648142236456660426480877 * 10 ^ 70 +
        1647601777715769998684672709201904162311467131196273669909111288520332) : ℚ) := by
  unfold recurrence2A6Square
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
    rw [show 64 = 21 +
      43 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_138_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_138_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_139_prefix_zero :
    (∑ x ∈ Finset.range 44,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (139 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (139 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_139_suffix_zero :
    (∑ x ∈ Finset.range 44,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (139 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_139 :
    recurrence2A6Square.coeff 139 =
      -((346628658535589655056205463 * 10 ^ 70 +
        9610755201393356926548120708086871053550590832854108271793665690771396) : ℚ) := by
  unfold recurrence2A6Square
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
    rw [show 64 = 20 +
      44 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_139_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_139_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_140_prefix_zero :
    (∑ x ∈ Finset.range 45,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (140 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (140 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_140_suffix_zero :
    (∑ x ∈ Finset.range 45,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (140 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_140 :
    recurrence2A6Square.coeff 140 =
      ((237609954660621772993415977 * 10 ^ 70 +
        9919101379875474345246721965576256692103212856432700568429915252116312) : ℚ) := by
  unfold recurrence2A6Square
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
    rw [show 64 = 19 +
      45 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_140_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_140_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_141_prefix_zero :
    (∑ x ∈ Finset.range 46,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (141 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (141 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_141_suffix_zero :
    (∑ x ∈ Finset.range 46,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (141 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_141 :
    recurrence2A6Square.coeff 141 =
      -((66902742358621423968943250 * 10 ^ 70 +
        5756424358761094667888784446728340829046519150158954321341504891470984) : ℚ) := by
  unfold recurrence2A6Square
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
    rw [show 64 = 18 +
      46 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_141_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_141_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_142_prefix_zero :
    (∑ x ∈ Finset.range 47,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (142 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (142 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_142_suffix_zero :
    (∑ x ∈ Finset.range 47,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (142 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_142 :
    recurrence2A6Square.coeff 142 =
      -((2027648424981982232336599 * 10 ^ 70 +
        1005669340093144806471378685383156650660960782502752657787806851053605) : ℚ) := by
  unfold recurrence2A6Square
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
    rw [show 64 = 17 +
      47 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_142_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_142_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_143_prefix_zero :
    (∑ x ∈ Finset.range 48,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (143 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (143 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_143_suffix_zero :
    (∑ x ∈ Finset.range 48,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (143 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_143 :
    recurrence2A6Square.coeff 143 =
      ((9636184391533143970001981 * 10 ^ 70 +
        7094136060562091255475854118418556182351699179600956797045569365664104) : ℚ) := by
  unfold recurrence2A6Square
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
    rw [show 64 = 16 +
      48 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_143_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_143_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_144_prefix_zero :
    (∑ x ∈ Finset.range 49,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (144 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (144 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_144_suffix_zero :
    (∑ x ∈ Finset.range 49,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (144 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_144 :
    recurrence2A6Square.coeff 144 =
      -((3773716820957857971356840 * 10 ^ 70 +
        2676127217316492341678615417323233969087977784249992941100370336207844) : ℚ) := by
  unfold recurrence2A6Square
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
    rw [show 64 = 15 +
      49 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_144_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_144_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_145_prefix_zero :
    (∑ x ∈ Finset.range 50,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (145 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (145 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_145_suffix_zero :
    (∑ x ∈ Finset.range 50,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (145 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_145 :
    recurrence2A6Square.coeff 145 =
      ((420139520843096825749227 * 10 ^ 70 +
        0662752438279389015814122651737843726454832758673852104238902110056282) : ℚ) := by
  unfold recurrence2A6Square
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
    rw [show 64 = 14 +
      50 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_145_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_145_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_146_prefix_zero :
    (∑ x ∈ Finset.range 51,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (146 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (146 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_146_suffix_zero :
    (∑ x ∈ Finset.range 51,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (146 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_146 :
    recurrence2A6Square.coeff 146 =
      ((219693742200345124347292 * 10 ^ 70 +
        5771190264538200913624663618337185057730471452864506250767823108209414) : ℚ) := by
  unfold recurrence2A6Square
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
    rw [show 64 = 13 +
      51 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_146_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_146_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_147_prefix_zero :
    (∑ x ∈ Finset.range 52,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (147 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (147 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_147_suffix_zero :
    (∑ x ∈ Finset.range 52,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (147 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_147 :
    recurrence2A6Square.coeff 147 =
      -((110171991573844955463331 * 10 ^ 70 +
        3944874677616526626827034263237791251579303254229454382217862094838894) : ℚ) := by
  unfold recurrence2A6Square
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
    rw [show 64 = 12 +
      52 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_147_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_147_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_148_prefix_zero :
    (∑ x ∈ Finset.range 53,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (148 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (148 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_148_suffix_zero :
    (∑ x ∈ Finset.range 53,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (148 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_148 :
    recurrence2A6Square.coeff 148 =
      ((15811683251184671783461 * 10 ^ 70 +
        6801167048311907326437775926529873885584518976494102051906245635339705) : ℚ) := by
  unfold recurrence2A6Square
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
    rw [show 64 = 11 +
      53 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_148_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_148_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_149_prefix_zero :
    (∑ x ∈ Finset.range 54,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (149 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (149 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_149_suffix_zero :
    (∑ x ∈ Finset.range 54,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (149 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_149 :
    recurrence2A6Square.coeff 149 =
      ((3634831929080460919410 * 10 ^ 70 +
        1395316653132712331976806443820663264715941732619172757632450291762362) : ℚ) := by
  unfold recurrence2A6Square
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
    rw [show 64 = 10 +
      54 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_149_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_149_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_150_prefix_zero :
    (∑ x ∈ Finset.range 55,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (150 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (150 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_150_suffix_zero :
    (∑ x ∈ Finset.range 55,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (150 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_150 :
    recurrence2A6Square.coeff 150 =
      -((1959791453390718160483 * 10 ^ 70 +
        2654305982163953950232147558707134119458724607780466000747459610981103) : ℚ) := by
  unfold recurrence2A6Square
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
    rw [show 64 = 9 +
      55 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_150_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_150_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_151_prefix_zero :
    (∑ x ∈ Finset.range 56,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (151 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (151 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_151_suffix_zero :
    (∑ x ∈ Finset.range 56,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (151 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_151 :
    recurrence2A6Square.coeff 151 =
      ((231445806406053258042 * 10 ^ 70 +
        2579256749176922351174426597623726023701190097945660165923773054545686) : ℚ) := by
  unfold recurrence2A6Square
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
    rw [show 64 = 8 +
      56 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_151_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_151_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_152_prefix_zero :
    (∑ x ∈ Finset.range 57,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (152 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (152 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_152_suffix_zero :
    (∑ x ∈ Finset.range 57,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (152 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_152 :
    recurrence2A6Square.coeff 152 =
      ((57354265163847392250 * 10 ^ 70 +
        3599972979534781033142824761736150248707344748021013782231929065827437) : ℚ) := by
  unfold recurrence2A6Square
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
    rw [show 64 = 7 +
      57 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_152_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_152_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_153_prefix_zero :
    (∑ x ∈ Finset.range 58,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (153 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (153 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_153_suffix_zero :
    (∑ x ∈ Finset.range 58,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (153 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_153 :
    recurrence2A6Square.coeff 153 =
      -((21473549176991168700 * 10 ^ 70 +
        2133933859591558863715038527281706016341056847599774742444828662766422) : ℚ) := by
  unfold recurrence2A6Square
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
    rw [show 64 = 6 +
      58 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_153_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_153_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_154_prefix_zero :
    (∑ x ∈ Finset.range 59,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (154 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (154 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_154_suffix_zero :
    (∑ x ∈ Finset.range 59,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (154 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_154 :
    recurrence2A6Square.coeff 154 =
      ((939627061153742726 * 10 ^ 70 +
        0324758135559438356484769656591606773391328928382789892886311456197983) : ℚ) := by
  unfold recurrence2A6Square
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
    rw [show 64 = 5 +
      59 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_154_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_154_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_155_prefix_zero :
    (∑ x ∈ Finset.range 60,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (155 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (155 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_155_suffix_zero :
    (∑ x ∈ Finset.range 60,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (155 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_155 :
    recurrence2A6Square.coeff 155 =
      ((695323824104038912 * 10 ^ 70 +
        1078894772772925598273501181249477944197973566164498505104346383019294) : ℚ) := by
  unfold recurrence2A6Square
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
    rw [show 64 = 4 +
      60 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_155_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_155_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_156_prefix_zero :
    (∑ x ∈ Finset.range 61,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (156 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (156 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_156_suffix_zero :
    (∑ x ∈ Finset.range 61,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (156 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_156 :
    recurrence2A6Square.coeff 156 =
      -((112099683268169003 * 10 ^ 70 +
        1828584562984532043462077544264231277696682360863365042577227341498685) : ℚ) := by
  unfold recurrence2A6Square
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
    rw [show 64 = 3 +
      61 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_156_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_156_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_157_prefix_zero :
    (∑ x ∈ Finset.range 62,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (157 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (157 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_157_suffix_zero :
    (∑ x ∈ Finset.range 62,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (157 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_157 :
    recurrence2A6Square.coeff 157 =
      -((10549606710433931 * 10 ^ 70 +
        2676189075594223218283564613911850325789109667514525597690429105653750) : ℚ) := by
  unfold recurrence2A6Square
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
    rw [show 64 = 2 +
      62 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_157_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_157_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_158_prefix_zero :
    (∑ x ∈ Finset.range 63,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (158 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (158 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_158_suffix_zero :
    (∑ x ∈ Finset.range 63,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (158 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_158 :
    recurrence2A6Square.coeff 158 =
      ((3796469627184103 * 10 ^ 70 +
        3997909656478104641580954045850972687495800885451171655246678605687349) : ℚ) := by
  unfold recurrence2A6Square
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
    rw [show 64 = 1 +
      63 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_158_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_158_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_159_prefix_zero :
    (∑ x ∈ Finset.range 64,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (159 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (159 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_159_suffix_zero :
    (∑ x ∈ Finset.range 64,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (159 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_159 :
    recurrence2A6Square.coeff 159 =
      ((44145171527900 * 10 ^ 70 +
        8822111061783059872982803458509065510517618692666189426903959826558450) : ℚ) := by
  unfold recurrence2A6Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 160 = 64 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_159_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_159_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_160_prefix_zero :
    (∑ x ∈ Finset.range 65,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (160 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (160 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_160_suffix_zero :
    (∑ x ∈ Finset.range 65,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (160 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_160 :
    recurrence2A6Square.coeff 160 =
      -((80847282173093 * 10 ^ 70 +
        7835662517247190691298075990425314168543179226431917247865100327269936) : ℚ) := by
  unfold recurrence2A6Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 161 = 65 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 31 +
      65 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_160_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_160_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_161_prefix_zero :
    (∑ x ∈ Finset.range 66,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (161 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (161 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_161_suffix_zero :
    (∑ x ∈ Finset.range 66,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (161 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_161 :
    recurrence2A6Square.coeff 161 =
      ((532382381945 * 10 ^ 70 +
        3774996989105203912141643391209689084517091545604964508977632801948522) : ℚ) := by
  unfold recurrence2A6Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 162 = 66 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 30 +
      66 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_161_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_161_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_162_prefix_zero :
    (∑ x ∈ Finset.range 67,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (162 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (162 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_162_suffix_zero :
    (∑ x ∈ Finset.range 67,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (162 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_162 :
    recurrence2A6Square.coeff 162 =
      ((1290900122053 * 10 ^ 70 +
        0540359493246816083877226819002887710623337442694270506831250313203426) : ℚ) := by
  unfold recurrence2A6Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 163 = 67 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 29 +
      67 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_162_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_162_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_163_prefix_zero :
    (∑ x ∈ Finset.range 68,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (163 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (163 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_163_suffix_zero :
    (∑ x ∈ Finset.range 68,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (163 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_163 :
    recurrence2A6Square.coeff 163 =
      ((17443326362 * 10 ^ 70 +
        8802981968490178891400995976071950417828278188299215947697901726074922) : ℚ) := by
  unfold recurrence2A6Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 164 = 68 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 28 +
      68 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_163_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_163_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_164_prefix_zero :
    (∑ x ∈ Finset.range 69,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (164 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (164 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_164_suffix_zero :
    (∑ x ∈ Finset.range 69,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (164 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_164 :
    recurrence2A6Square.coeff 164 =
      -((14799589540 * 10 ^ 70 +
        4970426887973858111791484352684643498912323812336197629650818335009747) : ℚ) := by
  unfold recurrence2A6Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 165 = 69 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 27 +
      69 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_164_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_164_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_165_prefix_zero :
    (∑ x ∈ Finset.range 70,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (165 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (165 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_165_suffix_zero :
    (∑ x ∈ Finset.range 70,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (165 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_165 :
    recurrence2A6Square.coeff 165 =
      -((965836432 * 10 ^ 70 +
        9066103247590071412024259283621727261983349424109450042040097288216728) : ℚ) := by
  unfold recurrence2A6Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 166 = 70 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 26 +
      70 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_165_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_165_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_166_prefix_zero :
    (∑ x ∈ Finset.range 71,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (166 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (166 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_166_suffix_zero :
    (∑ x ∈ Finset.range 71,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (166 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_166 :
    recurrence2A6Square.coeff 166 =
      ((62423256 * 10 ^ 70 +
        6785407395204608485061124802241877792579740818144894861367225382725668) : ℚ) := by
  unfold recurrence2A6Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 167 = 71 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 25 +
      71 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_166_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_166_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_167_prefix_zero :
    (∑ x ∈ Finset.range 72,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (167 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (167 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_167_suffix_zero :
    (∑ x ∈ Finset.range 72,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (167 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_167 :
    recurrence2A6Square.coeff 167 =
      ((12485087 * 10 ^ 70 +
        6455873400828609039242896258460198944106831775552323858623187599084854) : ℚ) := by
  unfold recurrence2A6Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 168 = 72 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 24 +
      72 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_167_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_167_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_168_prefix_zero :
    (∑ x ∈ Finset.range 73,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (168 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (168 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_168_suffix_zero :
    (∑ x ∈ Finset.range 73,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (168 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_168 :
    recurrence2A6Square.coeff 168 =
      ((870192 * 10 ^ 70 +
        3726163753722556092074410021439121397065593083239918486409516888683935) : ℚ) := by
  unfold recurrence2A6Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 169 = 73 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 23 +
      73 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_168_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_168_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_169_prefix_zero :
    (∑ x ∈ Finset.range 74,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (169 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (169 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_169_suffix_zero :
    (∑ x ∈ Finset.range 74,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (169 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_169 :
    recurrence2A6Square.coeff 169 =
      ((36139 * 10 ^ 70 +
        3867458181563524324402025985284329336011479382392748608773189059087622) : ℚ) := by
  unfold recurrence2A6Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 170 = 74 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 22 +
      74 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_169_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_169_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_170_prefix_zero :
    (∑ x ∈ Finset.range 75,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (170 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (170 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_170_suffix_zero :
    (∑ x ∈ Finset.range 75,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (170 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_170 :
    recurrence2A6Square.coeff 170 =
      ((1001 * 10 ^ 70 +
        3293499214398569764698475323857132964495674879453167906193089171680871) : ℚ) := by
  unfold recurrence2A6Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 171 = 75 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 21 +
      75 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_170_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_170_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_171_prefix_zero :
    (∑ x ∈ Finset.range 76,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (171 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (171 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_171_suffix_zero :
    (∑ x ∈ Finset.range 76,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (171 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_171 :
    recurrence2A6Square.coeff 171 =
      ((19 * 10 ^ 70 +
        2816962669947636576838893661226154833902623872216267059600835107103048) : ℚ) := by
  unfold recurrence2A6Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 172 = 76 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 20 +
      76 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_171_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_171_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_172_prefix_zero :
    (∑ x ∈ Finset.range 77,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (172 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (172 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_172_suffix_zero :
    (∑ x ∈ Finset.range 77,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (172 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_172 :
    recurrence2A6Square.coeff 172 =
      (2615224162398390719098475829411226888708020055345113699077848266151472 : ℚ) := by
  unfold recurrence2A6Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 173 = 77 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 19 +
      77 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_172_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_172_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_173_prefix_zero :
    (∑ x ∈ Finset.range 78,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (173 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (173 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_173_suffix_zero :
    (∑ x ∈ Finset.range 78,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (173 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_173 :
    recurrence2A6Square.coeff 173 =
      (24889277920344769480021071792469514258998696266452963094537772255180 : ℚ) := by
  unfold recurrence2A6Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 174 = 78 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 18 +
      78 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_173_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_173_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_174_prefix_zero :
    (∑ x ∈ Finset.range 79,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (174 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (174 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_174_suffix_zero :
    (∑ x ∈ Finset.range 79,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (174 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_174 :
    recurrence2A6Square.coeff 174 =
      (162488655451199352491806887916045153362086082249771862156168746739 : ℚ) := by
  unfold recurrence2A6Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 175 = 79 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 17 +
      79 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_174_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_174_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_175_prefix_zero :
    (∑ x ∈ Finset.range 80,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (175 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (175 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_175_suffix_zero :
    (∑ x ∈ Finset.range 80,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (175 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_175 :
    recurrence2A6Square.coeff 175 =
      (686040880325383882060660590215093782731011694876141864730323040 : ℚ) := by
  unfold recurrence2A6Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 176 = 80 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 16 +
      80 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_175_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_175_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_176_prefix_zero :
    (∑ x ∈ Finset.range 81,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (176 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (176 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_176_suffix_zero :
    (∑ x ∈ Finset.range 81,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (176 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_176 :
    recurrence2A6Square.coeff 176 =
      (1559123060787073316466672134097351087350401498378246870576712 : ℚ) := by
  unfold recurrence2A6Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 177 = 81 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 15 +
      81 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_176_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_176_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_177_prefix_zero :
    (∑ x ∈ Finset.range 82,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (177 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (177 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_177_suffix_zero :
    (∑ x ∈ Finset.range 82,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (177 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_177 :
    recurrence2A6Square.coeff 177 =
      (8401481899677902404145661808720760013201354775025217946 : ℚ) := by
  unfold recurrence2A6Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 178 = 82 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 14 +
      82 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_177_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_177_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_178_prefix_zero :
    (∑ x ∈ Finset.range 83,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (178 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (178 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_178_suffix_zero :
    (∑ x ∈ Finset.range 83,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (178 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_178 :
    recurrence2A6Square.coeff 178 =
      (-10304805384586832621040277078079810784518099330663493481 : ℚ) := by
  unfold recurrence2A6Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 179 = 83 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 13 +
      83 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_178_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_178_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_179_prefix_zero :
    (∑ x ∈ Finset.range 84,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (179 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (179 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_179_suffix_zero :
    (∑ x ∈ Finset.range 84,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (179 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_179 :
    recurrence2A6Square.coeff 179 =
      (-24828514004564765400398003669840017235722127410540778 : ℚ) := by
  unfold recurrence2A6Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 180 = 84 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 12 +
      84 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_179_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_179_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_180_prefix_zero :
    (∑ x ∈ Finset.range 85,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (180 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (180 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_180_suffix_zero :
    (∑ x ∈ Finset.range 85,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (180 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_180 :
    recurrence2A6Square.coeff 180 =
      (-12023827974796028314946333292508109809665216876518 : ℚ) := by
  unfold recurrence2A6Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 181 = 85 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 11 +
      85 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_180_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_180_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_181_prefix_zero :
    (∑ x ∈ Finset.range 86,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (181 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (181 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_181_suffix_zero :
    (∑ x ∈ Finset.range 86,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (181 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_181 :
    recurrence2A6Square.coeff 181 =
      (40318631455961320092606746485786684469023963208 : ℚ) := by
  unfold recurrence2A6Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 182 = 86 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 10 +
      86 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_181_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_181_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_182_prefix_zero :
    (∑ x ∈ Finset.range 87,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (182 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (182 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_182_suffix_zero :
    (∑ x ∈ Finset.range 87,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (182 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_182 :
    recurrence2A6Square.coeff 182 =
      (72185023597790658136703245581859655425361297 : ℚ) := by
  unfold recurrence2A6Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 183 = 87 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 9 +
      87 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_182_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_182_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_183_prefix_zero :
    (∑ x ∈ Finset.range 88,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (183 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (183 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_183_suffix_zero :
    (∑ x ∈ Finset.range 88,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (183 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_183 :
    recurrence2A6Square.coeff 183 =
      (46031155716271797980321886589999311997188 : ℚ) := by
  unfold recurrence2A6Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 184 = 88 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 8 +
      88 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_183_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_183_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_184_prefix_zero :
    (∑ x ∈ Finset.range 89,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (184 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (184 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_184_suffix_zero :
    (∑ x ∈ Finset.range 89,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (184 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_184 :
    recurrence2A6Square.coeff 184 =
      (12453926677689844657153159903133181453 : ℚ) := by
  unfold recurrence2A6Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 185 = 89 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 7 +
      89 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_184_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_184_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_185_prefix_zero :
    (∑ x ∈ Finset.range 90,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (185 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (185 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_185_suffix_zero :
    (∑ x ∈ Finset.range 90,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (185 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_185 :
    recurrence2A6Square.coeff 185 =
      (1242692394605797304168861943182276 : ℚ) := by
  unfold recurrence2A6Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 186 = 90 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 6 +
      90 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_185_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_185_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_186_prefix_zero :
    (∑ x ∈ Finset.range 91,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (186 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (186 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_186_suffix_zero :
    (∑ x ∈ Finset.range 91,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (186 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_186 :
    recurrence2A6Square.coeff 186 =
      (43662008488860887463177182721 : ℚ) := by
  unfold recurrence2A6Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 187 = 91 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 5 +
      91 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_186_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_186_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_187_prefix_zero :
    (∑ x ∈ Finset.range 92,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (187 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (187 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_187_suffix_zero :
    (∑ x ∈ Finset.range 92,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (187 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_187 :
    recurrence2A6Square.coeff 187 =
      (251109363763700586884208 : ℚ) := by
  unfold recurrence2A6Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 188 = 92 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 4 +
      92 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_187_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_187_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_188_prefix_zero :
    (∑ x ∈ Finset.range 93,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (188 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (188 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_188_suffix_zero :
    (∑ x ∈ Finset.range 93,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (188 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_188 :
    recurrence2A6Square.coeff 188 =
      (396784197563474483 : ℚ) := by
  unfold recurrence2A6Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 189 = 93 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 3 +
      93 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_188_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_188_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_189_prefix_zero :
    (∑ x ∈ Finset.range 94,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (189 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (189 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_189_suffix_zero :
    (∑ x ∈ Finset.range 94,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (189 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_189 :
    recurrence2A6Square.coeff 189 =
      (1259182850 : ℚ) := by
  unfold recurrence2A6Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 190 = 94 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 2 +
      94 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_189_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_189_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2A6Square_coeff_190_prefix_zero :
    (∑ x ∈ Finset.range 95,
      remainder2Coefficient6.coeff x * remainder2Coefficient6.coeff (190 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (190 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2A6Square_coeff_190_suffix_zero :
    (∑ x ∈ Finset.range 95,
      remainder2Coefficient6.coeff (96 + x) *
        remainder2Coefficient6.coeff (190 - (96 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A6_coeff_high (96 + x) (by omega)]
  norm_num

theorem recurrence2A6Square_coeff_190 :
    recurrence2A6Square.coeff 190 =
      (1 : ℚ) := by
  unfold recurrence2A6Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 191 = 95 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 1 +
      95 by norm_num, Finset.sum_range_add]
  rw [recurrence2A6Square_coeff_190_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2A6Square_coeff_190_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
