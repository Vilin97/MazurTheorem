/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB5
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupLeadingSquarePart0Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: LeadingSquare coefficient convolution

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
