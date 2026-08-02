/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupB2
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 5 lookup certificate: LeadingSquare coefficient convolution

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence5B2_coeff_0
  recurrence5B2_coeff_1
  recurrence5B2_coeff_2
  recurrence5B2_coeff_3
  recurrence5B2_coeff_4
  recurrence5B2_coeff_5
  recurrence5B2_coeff_6
  recurrence5B2_coeff_7
  recurrence5B2_coeff_8
  recurrence5B2_coeff_9
  recurrence5B2_coeff_10
  recurrence5B2_coeff_11
  recurrence5B2_coeff_12
  recurrence5B2_coeff_13
  recurrence5B2_coeff_14
  recurrence5B2_coeff_15
  recurrence5B2_coeff_16
  recurrence5B2_coeff_17
  recurrence5B2_coeff_18
  recurrence5B2_coeff_19
  recurrence5B2_coeff_20
  recurrence5B2_coeff_21
  recurrence5B2_coeff_22
  recurrence5B2_coeff_23
  recurrence5B2_coeff_24
  recurrence5B2_coeff_25
  recurrence5B2_coeff_26
  recurrence5B2_coeff_27
  recurrence5B2_coeff_28
  recurrence5B2_coeff_29
  recurrence5B2_coeff_30
  recurrence5B2_coeff_31
  recurrence5B2_coeff_32
  recurrence5B2_coeff_33
  recurrence5B2_coeff_34
  recurrence5B2_coeff_35
  recurrence5B2_coeff_36
  recurrence5B2_coeff_37
  recurrence5B2_coeff_38
  recurrence5B2_coeff_39
  recurrence5B2_coeff_40
  recurrence5B2_coeff_41
  recurrence5B2_coeff_42
  recurrence5B2_coeff_43
  recurrence5B2_coeff_44
  recurrence5B2_coeff_45
  recurrence5B2_coeff_46
  recurrence5B2_coeff_47
  recurrence5B2_coeff_48
  recurrence5B2_coeff_49
  recurrence5B2_coeff_50
  recurrence5B2_coeff_51
  recurrence5B2_coeff_52
  recurrence5B2_coeff_53
  recurrence5B2_coeff_54
  recurrence5B2_coeff_55
  recurrence5B2_coeff_56
  recurrence5B2_coeff_57
  recurrence5B2_coeff_58
  recurrence5B2_coeff_59
  recurrence5B2_coeff_60
  recurrence5B2_coeff_61
  recurrence5B2_coeff_62
  recurrence5B2_coeff_63

attribute [local simp]
  recurrence5B2_coeff_64
  recurrence5B2_coeff_65
  recurrence5B2_coeff_66
  recurrence5B2_coeff_67
  recurrence5B2_coeff_68
  recurrence5B2_coeff_69
  recurrence5B2_coeff_70
  recurrence5B2_coeff_71
  recurrence5B2_coeff_72
  recurrence5B2_coeff_73
  recurrence5B2_coeff_74
  recurrence5B2_coeff_75
  recurrence5B2_coeff_76
  recurrence5B2_coeff_77
  recurrence5B2_coeff_78
  recurrence5B2_coeff_79
  recurrence5B2_coeff_80
  recurrence5B2_coeff_81
  recurrence5B2_coeff_82
  recurrence5B2_coeff_83
  recurrence5B2_coeff_84
  recurrence5B2_coeff_85
  recurrence5B2_coeff_86
  recurrence5B2_coeff_87
  recurrence5B2_coeff_88
  recurrence5B2_coeff_89
  recurrence5B2_coeff_90
  recurrence5B2_coeff_91
  recurrence5B2_coeff_92
  recurrence5B2_coeff_93
  recurrence5B2_coeff_94
  recurrence5B2_coeff_95
  recurrence5B2_coeff_96
  recurrence5B2_coeff_97
  recurrence5B2_coeff_98
  recurrence5B2_coeff_99
  recurrence5B2_coeff_100
  recurrence5B2_coeff_101
  recurrence5B2_coeff_102
  recurrence5B2_coeff_103
  recurrence5B2_coeff_104
  recurrence5B2_coeff_105
  recurrence5B2_coeff_106
  recurrence5B2_coeff_107
  recurrence5B2_coeff_108
  recurrence5B2_coeff_109
  recurrence5B2_coeff_110
  recurrence5B2_coeff_111
  recurrence5B2_coeff_112
  recurrence5B2_coeff_113
  recurrence5B2_coeff_114
  recurrence5B2_coeff_115
  recurrence5B2_coeff_116
  recurrence5B2_coeff_117
  recurrence5B2_coeff_118
  recurrence5B2_coeff_119
  recurrence5B2_coeff_120
  recurrence5B2_coeff_121
  recurrence5B2_coeff_122
  recurrence5B2_coeff_123
  recurrence5B2_coeff_124
  recurrence5B2_coeff_125
  recurrence5B2_coeff_126
  recurrence5B2_coeff_127

attribute [local simp]
  recurrence5B2_coeff_128
  recurrence5B2_coeff_129
  recurrence5B2_coeff_130
  recurrence5B2_coeff_131
  recurrence5B2_coeff_132
  recurrence5B2_coeff_133
  recurrence5B2_coeff_134
  recurrence5B2_coeff_135
  recurrence5B2_coeff_136
  recurrence5B2_coeff_137
  recurrence5B2_coeff_138
  recurrence5B2_coeff_139
  recurrence5B2_coeff_140
  recurrence5B2_coeff_141
  recurrence5B2_coeff_142
  recurrence5B2_coeff_143
  recurrence5B2_coeff_144
  recurrence5B2_coeff_145

private theorem recurrence5LeadingSquare_coeff_218_prefix_zero :
    (∑ x ∈ Finset.range 73,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (218 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (218 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_218_suffix_zero :
    (∑ x ∈ Finset.range 73,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (218 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_218 :
    recurrence5LeadingSquare.coeff 218 =
      ((((81888530764874739740341 * 10 ^ 70 +
        7448307518375812225343963933062442897857985086394340288397721983463445) * 10 ^ 70 +
        9144336809192446654662787553022309784220927740541833012616475522198321) * 10 ^ 70 +
        4171597757231694084823943402177891412219503721080704946379825849275046) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 219 = 73 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 9 +
      73 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_218_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_218_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_219_prefix_zero :
    (∑ x ∈ Finset.range 74,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (219 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (219 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_219_suffix_zero :
    (∑ x ∈ Finset.range 74,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (219 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_219 :
    recurrence5LeadingSquare.coeff 219 =
      -((((32148804163660953413976 * 10 ^ 70 +
        4101281855143790333203587427938025987071876480544792410397234997291577) * 10 ^ 70 +
        2929815805724209827424211716146291569008937859123050203976630180589609) * 10 ^ 70 +
        4280672345969462919273419011466295107168886614447231251408328605626552) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 220 = 74 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 8 +
      74 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_219_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_219_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_220_prefix_zero :
    (∑ x ∈ Finset.range 75,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (220 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (220 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_220_suffix_zero :
    (∑ x ∈ Finset.range 75,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (220 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_220 :
    recurrence5LeadingSquare.coeff 220 =
      ((((12242886547216904623572 * 10 ^ 70 +
        3212174861919408612428046591430468993474923551523839342005051121935576) * 10 ^ 70 +
        8444840995728600633926094061352886342918570224060687135477108193883304) * 10 ^ 70 +
        9366627914241616911106157488376040245175795841115592024579686431242168) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 221 = 75 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 7 +
      75 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_220_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_220_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_221_prefix_zero :
    (∑ x ∈ Finset.range 76,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (221 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (221 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_221_suffix_zero :
    (∑ x ∈ Finset.range 76,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (221 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_221 :
    recurrence5LeadingSquare.coeff 221 =
      -((((4524849302534800460484 * 10 ^ 70 +
        3005209373993627861047641806088496583204550985134232073174481765700701) * 10 ^ 70 +
        8256338331111918647174864742242691332054764002682656599439026350936177) * 10 ^ 70 +
        9573599075600182866376984959674338931759431801104597092504222911151490) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 222 = 76 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 6 +
      76 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_221_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_221_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_222_prefix_zero :
    (∑ x ∈ Finset.range 77,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (222 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (222 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_222_suffix_zero :
    (∑ x ∈ Finset.range 77,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (222 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_222 :
    recurrence5LeadingSquare.coeff 222 =
      ((((1623223574361413893018 * 10 ^ 70 +
        6932422430306289347191204652529868187152205113347606875267453574497492) * 10 ^ 70 +
        8013831726298180314762903379067878528388153150413479001485137768268665) * 10 ^ 70 +
        8856341106365105493861907501847020942697597406231736792906448002696048) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 223 = 77 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 5 +
      77 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_222_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_222_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_223_prefix_zero :
    (∑ x ∈ Finset.range 78,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (223 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (223 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_223_suffix_zero :
    (∑ x ∈ Finset.range 78,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (223 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_223 :
    recurrence5LeadingSquare.coeff 223 =
      -((((565108282081861307055 * 10 ^ 70 +
        0566446581885782702227050445555262613868745505975491819982605645030504) * 10 ^ 70 +
        2957678079438812784049638004236732203627219724869442799483978748221409) * 10 ^ 70 +
        0672417060820655668063355395907732344968088555241795782238655728214118) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 224 = 78 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 4 +
      78 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_223_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_223_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_224_prefix_zero :
    (∑ x ∈ Finset.range 79,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (224 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (224 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_224_suffix_zero :
    (∑ x ∈ Finset.range 79,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (224 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_224 :
    recurrence5LeadingSquare.coeff 224 =
      ((((190858597937498866296 * 10 ^ 70 +
        8507205552132471450964756303173267897233603310589847862487690788173077) * 10 ^ 70 +
        9044430939775941719815222017795503981202943749567807704528012105888697) * 10 ^ 70 +
        1692560110304247201649327963061572693401489212980284882201178022419555) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 225 = 79 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 3 +
      79 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_224_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_224_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_225_prefix_zero :
    (∑ x ∈ Finset.range 80,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (225 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (225 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_225_suffix_zero :
    (∑ x ∈ Finset.range 80,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (225 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_225 :
    recurrence5LeadingSquare.coeff 225 =
      -((((62508662812328048641 * 10 ^ 70 +
        2289617420230765777123037472327716505217576734685916030943184738515218) * 10 ^ 70 +
        2354783462093490106179024176441657844106586979735413963538252685690740) * 10 ^ 70 +
        4545316055162180203876454983036489591272063323075994958793865609824430) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 226 = 80 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 2 +
      80 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_225_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_225_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_226_prefix_zero :
    (∑ x ∈ Finset.range 81,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (226 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (226 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_226_suffix_zero :
    (∑ x ∈ Finset.range 81,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (226 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_226 :
    recurrence5LeadingSquare.coeff 226 =
      ((((19845443449297371743 * 10 ^ 70 +
        6190563491077673939458205895861322638894542669225048395217940932565028) * 10 ^ 70 +
        7132436059950817506403144494155319050777831222814883123816315532603666) * 10 ^ 70 +
        6214655692897272260693280069291311680810098052066461165738126009305731) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 227 = 81 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 1 +
      81 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_226_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_226_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_227_prefix_zero :
    (∑ x ∈ Finset.range 82,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (227 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (227 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_227_suffix_zero :
    (∑ x ∈ Finset.range 82,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (227 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_227 :
    recurrence5LeadingSquare.coeff 227 =
      -((((6106270824628910291 * 10 ^ 70 +
        9441137849695525237140870878014700625844710836071305832218955617307382) * 10 ^ 70 +
        1905960596432489695947587037067016643581990132075726068950228890978066) * 10 ^ 70 +
        5515085186996831838670644286233379347372219435248227287694601461027674) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 228 = 82 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_227_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_227_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_228_prefix_zero :
    (∑ x ∈ Finset.range 83,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (228 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (228 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_228_suffix_zero :
    (∑ x ∈ Finset.range 83,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (228 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_228 :
    recurrence5LeadingSquare.coeff 228 =
      ((((1820804490318386643 * 10 ^ 70 +
        7796052422452642053843171547792764271786861478420955441514541440843363) * 10 ^ 70 +
        0675529360013310876591371959359219693228929918963448047160592178189289) * 10 ^ 70 +
        4176931859410970028827013230625660855906317104903186251914231352519969) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 229 = 83 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 31 +
      83 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_228_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_228_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_229_prefix_zero :
    (∑ x ∈ Finset.range 84,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (229 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (229 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_229_suffix_zero :
    (∑ x ∈ Finset.range 84,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (229 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_229 :
    recurrence5LeadingSquare.coeff 229 =
      -((((526208150670652503 * 10 ^ 70 +
        8056098303476670655549837240029525849261857214548909888317366925416747) * 10 ^ 70 +
        7898948850462443275675547005017208071124795757027757354493114077145501) * 10 ^ 70 +
        9739753914543172349612324204905152586830198918074095648277795974231512) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 230 = 84 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 30 +
      84 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_229_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_229_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_230_prefix_zero :
    (∑ x ∈ Finset.range 85,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (230 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (230 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_230_suffix_zero :
    (∑ x ∈ Finset.range 85,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (230 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_230 :
    recurrence5LeadingSquare.coeff 230 =
      ((((147396674107601551 * 10 ^ 70 +
        4177997529454317890508185487958597104432407232613573231996095690437761) * 10 ^ 70 +
        5058391558685212494174756477368608663138185582520739324849694834752690) * 10 ^ 70 +
        7990756754303619249298685957727760602718187105006127494993190108393506) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 231 = 85 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 29 +
      85 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_230_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_230_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_231_prefix_zero :
    (∑ x ∈ Finset.range 86,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (231 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (231 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_231_suffix_zero :
    (∑ x ∈ Finset.range 86,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (231 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_231 :
    recurrence5LeadingSquare.coeff 231 =
      -((((40008656051955752 * 10 ^ 70 +
        5316821138488317231292947110484588059461425753619588850703993851192491) * 10 ^ 70 +
        2915697476625560346560804510326610564338871246308376748484496494549015) * 10 ^ 70 +
        2076290681042936384667172930470425010151184188329795994255281141209832) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 232 = 86 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 28 +
      86 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_231_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_231_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_232_prefix_zero :
    (∑ x ∈ Finset.range 87,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (232 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (232 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_232_suffix_zero :
    (∑ x ∈ Finset.range 87,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (232 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_232 :
    recurrence5LeadingSquare.coeff 232 =
      ((((10513333949672732 * 10 ^ 70 +
        8800453791117957228272907305831102932009688306823985065275774234343977) * 10 ^ 70 +
        0916679591629657743833856563836710898494751090564147063256594163475581) * 10 ^ 70 +
        2328509367451933110615788999073969521727980333591352414806615166045339) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 233 = 87 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 27 +
      87 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_232_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_232_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_233_prefix_zero :
    (∑ x ∈ Finset.range 88,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (233 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (233 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_233_suffix_zero :
    (∑ x ∈ Finset.range 88,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (233 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_233 :
    recurrence5LeadingSquare.coeff 233 =
      -((((2668463835174063 * 10 ^ 70 +
        1086121521917914253549886055046861857145757653397907155207342688727565) * 10 ^ 70 +
        0871793226382329397767144115128639084104976216366478168238267515625244) * 10 ^ 70 +
        7711113131879504683075786097840622661130177178343879902486648104128970) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 234 = 88 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 26 +
      88 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_233_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_233_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_234_prefix_zero :
    (∑ x ∈ Finset.range 89,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (234 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (234 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_234_suffix_zero :
    (∑ x ∈ Finset.range 89,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (234 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_234 :
    recurrence5LeadingSquare.coeff 234 =
      ((((651384931309350 * 10 ^ 70 +
        2310059560922150248777910446893453265929103322755721366020390124893624) * 10 ^ 70 +
        3622401491979464978128098830364830665633731073220302169067693484833079) * 10 ^ 70 +
        7329820102168919510756198313573504140264739358245714137926567805056092) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 235 = 89 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 25 +
      89 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_234_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_234_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_235_prefix_zero :
    (∑ x ∈ Finset.range 90,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (235 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (235 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_235_suffix_zero :
    (∑ x ∈ Finset.range 90,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (235 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_235 :
    recurrence5LeadingSquare.coeff 235 =
      -((((151799496916364 * 10 ^ 70 +
        9648507957049708972879824958738751796509929454558309857491822336067927) * 10 ^ 70 +
        1118773054829368075278160111388240066547341590115217919886227347917628) * 10 ^ 70 +
        5328077894800225494188037112903562714526489820388053981475556362301544) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 236 = 90 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 24 +
      90 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_235_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_235_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_236_prefix_zero :
    (∑ x ∈ Finset.range 91,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (236 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (236 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_236_suffix_zero :
    (∑ x ∈ Finset.range 91,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (236 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_236 :
    recurrence5LeadingSquare.coeff 236 =
      ((((33371281688227 * 10 ^ 70 +
        4499946884101513635470703020198964053398389981107525283875291703408246) * 10 ^ 70 +
        6306118394845954645195140480069093576403470339915582690255887946003932) * 10 ^ 70 +
        1412108316487231539409574780860121938744343887049226869291395299550682) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 237 = 91 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 23 +
      91 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_236_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_236_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_237_prefix_zero :
    (∑ x ∈ Finset.range 92,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (237 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (237 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_237_suffix_zero :
    (∑ x ∈ Finset.range 92,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (237 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_237 :
    recurrence5LeadingSquare.coeff 237 =
      -((((6786508807025 * 10 ^ 70 +
        5556619465154202035334015445779428946459462155474091181077325795191549) * 10 ^ 70 +
        0074671776888413525387486213559344860644525157615685237028802155049352) * 10 ^ 70 +
        6305791355515910315731973576775730756647746664269908807476742343075436) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 238 = 92 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 22 +
      92 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_237_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_237_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_238_prefix_zero :
    (∑ x ∈ Finset.range 93,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (238 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (238 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_238_suffix_zero :
    (∑ x ∈ Finset.range 93,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (238 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_238 :
    recurrence5LeadingSquare.coeff 238 =
      ((((1232816524579 * 10 ^ 70 +
        5633416648267137786924547814581404769258513050038473166315775123683857) * 10 ^ 70 +
        7075380469851173345883684852694410189898567340504409809552402463026689) * 10 ^ 70 +
        4213558309756920657397021038035242849850655314453629655141701574952814) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 239 = 93 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 21 +
      93 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_238_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_238_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_239_prefix_zero :
    (∑ x ∈ Finset.range 94,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (239 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (239 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_239_suffix_zero :
    (∑ x ∈ Finset.range 94,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (239 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_239 :
    recurrence5LeadingSquare.coeff 239 =
      -((((185229589525 * 10 ^ 70 +
        4704903808411773791272603498738499585440607043030312220445718536103999) * 10 ^ 70 +
        6603427355955384779728713793907679667266846235633550060213243427220453) * 10 ^ 70 +
        0872489242862674043456127825175255176570713700649480041586169087970692) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 240 = 94 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 20 +
      94 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_239_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_239_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_240_prefix_zero :
    (∑ x ∈ Finset.range 95,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (240 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (240 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_240_suffix_zero :
    (∑ x ∈ Finset.range 95,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (240 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_240 :
    recurrence5LeadingSquare.coeff 240 =
      ((((17492311777 * 10 ^ 70 +
        1659969140044333813682158685713139057026490182531775494053875883875203) * 10 ^ 70 +
        7034019953076778458957832603320366669239013055391038522438514372174488) * 10 ^ 70 +
        7612898467315112626242831734747506648992903235306876432129074348450723) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 241 = 95 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 19 +
      95 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_240_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_240_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_241_prefix_zero :
    (∑ x ∈ Finset.range 96,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (241 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (241 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_241_suffix_zero :
    (∑ x ∈ Finset.range 96,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (241 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_241 :
    recurrence5LeadingSquare.coeff 241 =
      ((((1466705916 * 10 ^ 70 +
        9360104866849474626917264060797916868068436657088163414699463305355470) * 10 ^ 70 +
        3228691129135444426107225536216537169206744847956204918743298862799991) * 10 ^ 70 +
        7437138864654511264568201920351597524591644071726831689581029232533406) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 242 = 96 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 18 +
      96 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_241_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_241_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_242_prefix_zero :
    (∑ x ∈ Finset.range 97,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (242 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (242 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_242_suffix_zero :
    (∑ x ∈ Finset.range 97,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (242 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_242 :
    recurrence5LeadingSquare.coeff 242 =
      -((((1353368732 * 10 ^ 70 +
        2756067656743234267368358346425291533239609201199385372489945645774170) * 10 ^ 70 +
        0239162876865021998904879702691844718070084274781417866018221283559503) * 10 ^ 70 +
        2177331087078178190768580668789631027302480432200756439990217648052944) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 243 = 97 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 17 +
      97 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_242_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_242_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_243_prefix_zero :
    (∑ x ∈ Finset.range 98,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (243 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (243 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_243_suffix_zero :
    (∑ x ∈ Finset.range 98,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (243 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_243 :
    recurrence5LeadingSquare.coeff 243 =
      ((((470751726 * 10 ^ 70 +
        7614944524826200531574579588175584920913784368273854283811864073102281) * 10 ^ 70 +
        0437195405547009050415779105802071893243302029464802864886173534320533) * 10 ^ 70 +
        1316454044001371634444609496313093919075859455744504869348302311572228) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 244 = 98 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 16 +
      98 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_243_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_243_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_244_prefix_zero :
    (∑ x ∈ Finset.range 99,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (244 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (244 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_244_suffix_zero :
    (∑ x ∈ Finset.range 99,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (244 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_244 :
    recurrence5LeadingSquare.coeff 244 =
      -((((131888258 * 10 ^ 70 +
        2940112353473702192172816940653508976384907902854623062081062771179190) * 10 ^ 70 +
        4555670752196544412092199959396816687873490981335920031749682179069067) * 10 ^ 70 +
        1961067861104444731076399270131411838356733773785385750972891939875629) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 245 = 99 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 15 +
      99 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_244_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_244_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_245_prefix_zero :
    (∑ x ∈ Finset.range 100,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (245 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (245 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_245_suffix_zero :
    (∑ x ∈ Finset.range 100,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (245 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_245 :
    recurrence5LeadingSquare.coeff 245 =
      ((((34696509 * 10 ^ 70 +
        0923761456219004808158726655146534932277246614671637588388556314320338) * 10 ^ 70 +
        1796201990077070761531759748788987609313509691043139991158486911109825) * 10 ^ 70 +
        5114172460508155656435265703753714015406374662706683209746276875751998) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 246 = 100 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 14 +
      100 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_245_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_245_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_246_prefix_zero :
    (∑ x ∈ Finset.range 101,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (246 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (246 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_246_suffix_zero :
    (∑ x ∈ Finset.range 101,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (246 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_246 :
    recurrence5LeadingSquare.coeff 246 =
      -((((8871171 * 10 ^ 70 +
        7716529267504777370243386392295963889416736025774439055378429752594471) * 10 ^ 70 +
        2676477548425245315949337784019681274416569311634869054291626885897188) * 10 ^ 70 +
        6235820448615492319221427631397743441024068124485241276225332675022236) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 247 = 101 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 13 +
      101 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_246_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_246_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_247_prefix_zero :
    (∑ x ∈ Finset.range 102,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (247 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (247 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_247_suffix_zero :
    (∑ x ∈ Finset.range 102,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (247 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_247 :
    recurrence5LeadingSquare.coeff 247 =
      ((((2053300 * 10 ^ 70 +
        9931745901040666300387029155381964219205667579866716893759003383868656) * 10 ^ 70 +
        5456509451724282552215983637317095328759632139313408108666213969982913) * 10 ^ 70 +
        4019099449453916343427423779697429996973830779964651469172311642252778) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 248 = 102 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 12 +
      102 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_247_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_247_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_248_prefix_zero :
    (∑ x ∈ Finset.range 103,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (248 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (248 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_248_suffix_zero :
    (∑ x ∈ Finset.range 103,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (248 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_248 :
    recurrence5LeadingSquare.coeff 248 =
      -((((353841 * 10 ^ 70 +
        0810120862520580865678035463101776983112969637707615397905007388941969) * 10 ^ 70 +
        7090085115690362993466322385690716356261679760221375389647480841855146) * 10 ^ 70 +
        9645109815833392643153031868183058991339434257224515964604129708580077) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 249 = 103 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 11 +
      103 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_248_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_248_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_249_prefix_zero :
    (∑ x ∈ Finset.range 104,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (249 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (249 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_249_suffix_zero :
    (∑ x ∈ Finset.range 104,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (249 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_249 :
    recurrence5LeadingSquare.coeff 249 =
      ((((13798 * 10 ^ 70 +
        7739853736306796978797542895660188177097100275874153091233387036686590) * 10 ^ 70 +
        3354349696183671086377185870876291349247374670922392999018655041646589) * 10 ^ 70 +
        5708154555074734067379728814508052820801923487297884015745479492898744) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 250 = 104 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 10 +
      104 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_249_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_249_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_250_prefix_zero :
    (∑ x ∈ Finset.range 105,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (250 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (250 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_250_suffix_zero :
    (∑ x ∈ Finset.range 105,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (250 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_250 :
    recurrence5LeadingSquare.coeff 250 =
      ((((18747 * 10 ^ 70 +
        9425242518544188810610013135676541383368951892067651813060620471023235) * 10 ^ 70 +
        2931076658704202535257178526040472875265985349865505125245637116790405) * 10 ^ 70 +
        7090494821446816079351409781937360652168537479440979380477076252752528) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 251 = 105 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 9 +
      105 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_250_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_250_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_251_prefix_zero :
    (∑ x ∈ Finset.range 106,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (251 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (251 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_251_suffix_zero :
    (∑ x ∈ Finset.range 106,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (251 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_251 :
    recurrence5LeadingSquare.coeff 251 =
      -((((8532 * 10 ^ 70 +
        4019788617147046105844078935575367637545598316280289839621484101540986) * 10 ^ 70 +
        3946517581582456356653043926321664533827947644640911228006644130893647) * 10 ^ 70 +
        6209595776817462594006731724205547949153405163581883142966383092535768) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 252 = 106 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 8 +
      106 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_251_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_251_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_252_prefix_zero :
    (∑ x ∈ Finset.range 107,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (252 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (252 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_252_suffix_zero :
    (∑ x ∈ Finset.range 107,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (252 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_252 :
    recurrence5LeadingSquare.coeff 252 =
      ((((2129 * 10 ^ 70 +
        9811940457477361332461509275628787415247511520481130312965988115941831) * 10 ^ 70 +
        8143855604553113834017391231508215073674185691215881712106336778166614) * 10 ^ 70 +
        1796363087451079382652967930068049989820106156606340762795845726617929) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 253 = 107 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 7 +
      107 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_252_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_252_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_253_prefix_zero :
    (∑ x ∈ Finset.range 108,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (253 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (253 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_253_suffix_zero :
    (∑ x ∈ Finset.range 108,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (253 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_253 :
    recurrence5LeadingSquare.coeff 253 =
      -((((297 * 10 ^ 70 +
        2221486975937982182199053576267216597774484890661305077278166074636967) * 10 ^ 70 +
        3963152610258238552856234857703133562712749381784182717039467438743384) * 10 ^ 70 +
        9202761144646684137852687623767957126910379922409350180447448599060022) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 254 = 108 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 6 +
      108 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_253_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_253_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_254_prefix_zero :
    (∑ x ∈ Finset.range 109,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (254 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (254 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_254_suffix_zero :
    (∑ x ∈ Finset.range 109,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (254 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_254 :
    recurrence5LeadingSquare.coeff 254 =
      -((((3 * 10 ^ 70 +
        8259876917311928351933227450557058833498496919586814444306270516073324) * 10 ^ 70 +
        8507084507727351757019226268564525746367402889045391426548374638738309) * 10 ^ 70 +
        2317965504182752771280937985142422763718001778185636544433143385920009) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 255 = 109 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 5 +
      109 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_254_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_254_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_255_prefix_zero :
    (∑ x ∈ Finset.range 110,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (255 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (255 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_255_suffix_zero :
    (∑ x ∈ Finset.range 110,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (255 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_255 :
    recurrence5LeadingSquare.coeff 255 =
      ((((13 * 10 ^ 70 +
        4922144131913098394192037441973470701457577262518701590711587827060422) * 10 ^ 70 +
        7135987938455436786828318188519124761890844629229647870100797986870285) * 10 ^ 70 +
        9004538620521838837736910298142833843722902412902805924334668644065338) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 256 = 110 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 4 +
      110 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_255_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_255_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_256_prefix_zero :
    (∑ x ∈ Finset.range 111,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (256 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (256 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_256_suffix_zero :
    (∑ x ∈ Finset.range 111,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (256 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_256 :
    recurrence5LeadingSquare.coeff 256 =
      -((((3 * 10 ^ 70 +
        5242808523442181726736881499618209878161573900674961754247509423109735) * 10 ^ 70 +
        5066214627098584833329436956602203827219759238428936226139841753466449) * 10 ^ 70 +
        1320124991076282664648730415157723271117709776258271676731566695017442) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 257 = 111 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 3 +
      111 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_256_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_256_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_257_prefix_zero :
    (∑ x ∈ Finset.range 112,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (257 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (257 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_257_suffix_zero :
    (∑ x ∈ Finset.range 112,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (257 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_257 :
    recurrence5LeadingSquare.coeff 257 =
      (((4345201613291971562329898925339718388518076369705450408971235948928965 * 10 ^ 70 +
        4732732633690035517061657705469820115734109051667918236323417074122418) * 10 ^ 70 +
        3527493983203024193854558474935266082582350650825860010822938044023638) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 258 = 112 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 2 +
      112 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_257_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_257_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_258_prefix_zero :
    (∑ x ∈ Finset.range 113,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (258 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (258 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_258_suffix_zero :
    (∑ x ∈ Finset.range 113,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (258 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_258 :
    recurrence5LeadingSquare.coeff 258 =
      (((35960166135586426253051199363256386278187404796170430047281563994635 * 10 ^ 70 +
        9128277879343513816449819990099616256235486055708722444560393087165145) * 10 ^ 70 +
        7857977590076344803779076601442180523761696462181506018791790755236303) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 259 = 113 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 1 +
      113 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_258_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_258_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_259_prefix_zero :
    (∑ x ∈ Finset.range 114,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (259 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (259 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_259_suffix_zero :
    (∑ x ∈ Finset.range 114,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (259 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_259 :
    recurrence5LeadingSquare.coeff 259 =
      -(((119765326763693282704173573483742289544040952806006968277701893094935 * 10 ^ 70 +
        6768896297598826632917458074691826549360712273188621645657454883982017) * 10 ^ 70 +
        8828702761263151141515468424462129534773814956728605278992988328121204) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 260 = 114 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_259_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_259_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_260_prefix_zero :
    (∑ x ∈ Finset.range 115,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (260 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (260 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_260_suffix_zero :
    (∑ x ∈ Finset.range 115,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (260 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_260 :
    recurrence5LeadingSquare.coeff 260 =
      (((22304728731049531113742368014001702798564075935124692929265956159497 * 10 ^ 70 +
        3921843874456025716624263574299334230516251185681354819550455762260376) * 10 ^ 70 +
        7331786578862846775313258563012737216389833365381327660305577596146810) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 261 = 115 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 31 +
      115 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_260_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_260_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_261_prefix_zero :
    (∑ x ∈ Finset.range 116,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (261 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (261 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_261_suffix_zero :
    (∑ x ∈ Finset.range 116,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (261 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_261 :
    recurrence5LeadingSquare.coeff 261 =
      -(((1646485830958721963376088354983931963122694771108153116548515929108 * 10 ^ 70 +
        5493343841254401527579992311892139012339334351650097789532819263669874) * 10 ^ 70 +
        9267457078046676766621547970944609893358123810029103319241286367517190) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 262 = 116 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 30 +
      116 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_261_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_261_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_262_prefix_zero :
    (∑ x ∈ Finset.range 117,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (262 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (262 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_262_suffix_zero :
    (∑ x ∈ Finset.range 117,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (262 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_262 :
    recurrence5LeadingSquare.coeff 262 =
      -(((80313300423283863433994152326932243407241711727599725262114188789 * 10 ^ 70 +
        4785416946367848867296912631310508481386695653110512734574197594140387) * 10 ^ 70 +
        4381881584031696362872456212784800411145521911035342888562111545453521) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 263 = 117 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 29 +
      117 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_262_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_262_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_263_prefix_zero :
    (∑ x ∈ Finset.range 118,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (263 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (263 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_263_suffix_zero :
    (∑ x ∈ Finset.range 118,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (263 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_263 :
    recurrence5LeadingSquare.coeff 263 =
      (((28009821839346070403131832942920555722713705716129793075656154622 * 10 ^ 70 +
        5004952053876280667994352200360264280600208941306247188670359830132276) * 10 ^ 70 +
        9852649414522293030568567462645868990431017277724108042464315877388828) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 264 = 118 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 28 +
      118 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_263_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_263_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_264_prefix_zero :
    (∑ x ∈ Finset.range 119,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (264 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (264 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_264_suffix_zero :
    (∑ x ∈ Finset.range 119,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (264 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_264 :
    recurrence5LeadingSquare.coeff 264 =
      -(((1867262200850581868221989986020511165990794917891741291599683684 * 10 ^ 70 +
        9957488429047850007052605323728116779946864633732992594374903906175395) * 10 ^ 70 +
        1749440594098695811546921961469153789361160421853996283181660271949309) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 265 = 119 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 27 +
      119 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_264_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_264_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_265_prefix_zero :
    (∑ x ∈ Finset.range 120,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (265 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (265 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_265_suffix_zero :
    (∑ x ∈ Finset.range 120,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (265 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_265 :
    recurrence5LeadingSquare.coeff 265 =
      -(((76764007451207735061695659522303265132845592130018926310912869 * 10 ^ 70 +
        8447276564775314986442193586230012339559963565518964670986280098878503) * 10 ^ 70 +
        3357389903218422517181740208119846324215357097918823852667133927587370) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 266 = 120 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 26 +
      120 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_265_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_265_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_266_prefix_zero :
    (∑ x ∈ Finset.range 121,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (266 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (266 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_266_suffix_zero :
    (∑ x ∈ Finset.range 121,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (266 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_266 :
    recurrence5LeadingSquare.coeff 266 =
      (((15552442431980793718426696537891120467484491145084214926922035 * 10 ^ 70 +
        7641998439637114138270732475898425319895766121078472743942203725086110) * 10 ^ 70 +
        2576204890080068061641804447241842027111145758893292747433944609171919) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 267 = 121 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 25 +
      121 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_266_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_266_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_267_prefix_zero :
    (∑ x ∈ Finset.range 122,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (267 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (267 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_267_suffix_zero :
    (∑ x ∈ Finset.range 122,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (267 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_267 :
    recurrence5LeadingSquare.coeff 267 =
      -(((181582325685393115925822629709923966265692494664141337208220 * 10 ^ 70 +
        7098303632699063711768952136099589565672954981421811897713311152600585) * 10 ^ 70 +
        6074469560724814627376739875934659287940527483479885138515865459983204) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 268 = 122 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 24 +
      122 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_267_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_267_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_268_prefix_zero :
    (∑ x ∈ Finset.range 123,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (268 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (268 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_268_suffix_zero :
    (∑ x ∈ Finset.range 123,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (268 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_268 :
    recurrence5LeadingSquare.coeff 268 =
      -(((53359396802790622447856003102727719479965136274932337512884 * 10 ^ 70 +
        9133231764669675828604067811437943782340697336317089747343738433275685) * 10 ^ 70 +
        5110129955564167751288451110258953465436774631986111070292466445769121) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 269 = 123 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 23 +
      123 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_268_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_268_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_269_prefix_zero :
    (∑ x ∈ Finset.range 124,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (269 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (269 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_269_suffix_zero :
    (∑ x ∈ Finset.range 124,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (269 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_269 :
    recurrence5LeadingSquare.coeff 269 =
      (((324795004245404797785314166954937406170636536536209205824 * 10 ^ 70 +
        8777730881228911745880297162577077625685972606063130738227578285366155) * 10 ^ 70 +
        1468094288047082485606655008701769733757973195498097726683661524740044) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 270 = 124 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 22 +
      124 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_269_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_269_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_270_prefix_zero :
    (∑ x ∈ Finset.range 125,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (270 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (270 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_270_suffix_zero :
    (∑ x ∈ Finset.range 125,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (270 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_270 :
    recurrence5LeadingSquare.coeff 270 =
      (((120669923289704179524290496986922510783778111748623161961 * 10 ^ 70 +
        8019218337492666803759771991668040340340316339399401449245565637889614) * 10 ^ 70 +
        2319944577114513981613940435211973881332197246213660408333259104343458) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 271 = 125 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 21 +
      125 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_270_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_270_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_271_prefix_zero :
    (∑ x ∈ Finset.range 126,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (271 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (271 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_271_suffix_zero :
    (∑ x ∈ Finset.range 126,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (271 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_271 :
    recurrence5LeadingSquare.coeff 271 =
      (((3953994136045601450571031333869285107193647587253239554 * 10 ^ 70 +
        8592683614129740009638240891221969272415687313009676721899553179842184) * 10 ^ 70 +
        5498146631367341398455074434639492114116890365679742022078021019855514) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 272 = 126 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 20 +
      126 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_271_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_271_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_272_prefix_zero :
    (∑ x ∈ Finset.range 127,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (272 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (272 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_272_suffix_zero :
    (∑ x ∈ Finset.range 127,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (272 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_272 :
    recurrence5LeadingSquare.coeff 272 =
      (((61764277594930197794540148729040413318181894922508837 * 10 ^ 70 +
        6959621755768740114898240151213200664064823369857839917669355219209034) * 10 ^ 70 +
        3682281851303466017045701337090061058556660030180378591097276577841077) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 273 = 127 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 19 +
      127 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_272_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_272_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_273_prefix_zero :
    (∑ x ∈ Finset.range 128,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (273 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (273 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_273_suffix_zero :
    (∑ x ∈ Finset.range 128,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (273 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_273 :
    recurrence5LeadingSquare.coeff 273 =
      (((547790642621037684234070411697493064622578520922235 * 10 ^ 70 +
        0576464990189177319023723900516673262080007171218159156302516361868274) * 10 ^ 70 +
        8852998616059788281749461852544485592790460965552639378386765574381732) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 274 = 128 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 18 +
      128 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_273_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_273_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_274_prefix_zero :
    (∑ x ∈ Finset.range 129,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (274 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (274 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_274_suffix_zero :
    (∑ x ∈ Finset.range 129,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (274 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_274 :
    recurrence5LeadingSquare.coeff 274 =
      (((2829662601640061287235287201287881571172125965553 * 10 ^ 70 +
        3500065701420122020089032935876909547108979746660134389803838623851338) * 10 ^ 70 +
        2762220511334277697621430234259884124434611049296103506532351329490142) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 275 = 129 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 17 +
      129 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_274_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_274_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_275_prefix_zero :
    (∑ x ∈ Finset.range 130,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (275 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (275 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_275_suffix_zero :
    (∑ x ∈ Finset.range 130,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (275 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_275 :
    recurrence5LeadingSquare.coeff 275 =
      (((7582295340510408945186420803951578525972152004 * 10 ^ 70 +
        8774054026864617010605678917177465492019975927230398986058950918642956) * 10 ^ 70 +
        0595658864090960899714140388547946696505683755940441226224156165646362) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 276 = 130 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 16 +
      130 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_275_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_275_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_276_prefix_zero :
    (∑ x ∈ Finset.range 131,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (276 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (276 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_276_suffix_zero :
    (∑ x ∈ Finset.range 131,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (276 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_276 :
    recurrence5LeadingSquare.coeff 276 =
      (((2663924128361890334986103599983769132803373 * 10 ^ 70 +
        6474450699833572220351242067005991541504385823494091945043645067923081) * 10 ^ 70 +
        2323652400683375802110247380436393884614805995403919100556087630793360) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 277 = 131 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 15 +
      131 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_276_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_276_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_277_prefix_zero :
    (∑ x ∈ Finset.range 132,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (277 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (277 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_277_suffix_zero :
    (∑ x ∈ Finset.range 132,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (277 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_277 :
    recurrence5LeadingSquare.coeff 277 =
      -(((44074376218403613883900606625072005331856 * 10 ^ 70 +
        2308877973332966221528925103127439608205499621439694772552341793169389) * 10 ^ 70 +
        2220310085011500095315501784326608109360360958032098408913057232419322) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 278 = 132 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 14 +
      132 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_277_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_277_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_278_prefix_zero :
    (∑ x ∈ Finset.range 133,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (278 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (278 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_278_suffix_zero :
    (∑ x ∈ Finset.range 133,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (278 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_278 :
    recurrence5LeadingSquare.coeff 278 =
      -(((114261943358635648316033596414097813552 * 10 ^ 70 +
        9533984949644212310184960505375793930828237752762349317726991018364738) * 10 ^ 70 +
        3860296490783191584383688092387556108986763069404672861005665059989682) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 279 = 133 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 13 +
      133 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_278_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_278_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_279_prefix_zero :
    (∑ x ∈ Finset.range 134,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (279 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (279 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_279_suffix_zero :
    (∑ x ∈ Finset.range 134,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (279 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_279 :
    recurrence5LeadingSquare.coeff 279 =
      -(((55176542370803465355598875734011037 * 10 ^ 70 +
        5867100190393238379351345826147861872159284518892985060912929876626512) * 10 ^ 70 +
        8620702151659370735501396272418249513504076605448537441600806728543380) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 280 = 134 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 12 +
      134 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_279_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_279_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_280_prefix_zero :
    (∑ x ∈ Finset.range 135,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (280 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (280 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_280_suffix_zero :
    (∑ x ∈ Finset.range 135,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (280 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_280 :
    recurrence5LeadingSquare.coeff 280 =
      (((184943866910294632472324647043940 * 10 ^ 70 +
        1874024000780392239406713194699801326685420199417086480998426782955325) * 10 ^ 70 +
        0306954919322979328909695202863713804873325588170712382308284515743810) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 281 = 135 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 11 +
      135 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_280_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_280_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_281_prefix_zero :
    (∑ x ∈ Finset.range 136,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (281 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (281 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_281_suffix_zero :
    (∑ x ∈ Finset.range 136,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (281 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_281 :
    recurrence5LeadingSquare.coeff 281 =
      (((310035831676609789988155830120 * 10 ^ 70 +
        9660143974085702777483877843583114335432224892667712479804955787769292) * 10 ^ 70 +
        3657663440974963200710861428003932872531384453579224273196252065201118) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 282 = 136 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 10 +
      136 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_281_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_281_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_282_prefix_zero :
    (∑ x ∈ Finset.range 137,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (282 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (282 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_282_suffix_zero :
    (∑ x ∈ Finset.range 137,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (282 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_282 :
    recurrence5LeadingSquare.coeff 282 =
      (((182519451272770922175397234 * 10 ^ 70 +
        3868708161574569838775041041823346419626647599693948078539765568145051) * 10 ^ 70 +
        3974642584411035667599348919688226810200111779666510752845830067769620) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 283 = 137 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 9 +
      137 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_282_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_282_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_283_prefix_zero :
    (∑ x ∈ Finset.range 138,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (283 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (283 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_283_suffix_zero :
    (∑ x ∈ Finset.range 138,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (283 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_283 :
    recurrence5LeadingSquare.coeff 283 =
      (((43699304076390472623474 * 10 ^ 70 +
        1616457978869304021202676589197469733081545906711728961406918802992970) * 10 ^ 70 +
        0473205136166276795097873318054857511277408792657697880923673854080252) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 284 = 138 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 8 +
      138 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_283_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_283_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_284_prefix_zero :
    (∑ x ∈ Finset.range 139,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (284 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (284 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_284_suffix_zero :
    (∑ x ∈ Finset.range 139,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (284 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_284 :
    recurrence5LeadingSquare.coeff 284 =
      (((4366330939965815064 * 10 ^ 70 +
        4627815406935611318270412671965762744125587805312798762431130808776968) * 10 ^ 70 +
        8936745247149639638760379828497683636683074039432751786507814260700729) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 285 = 139 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 7 +
      139 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_284_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_284_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_285_prefix_zero :
    (∑ x ∈ Finset.range 140,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (285 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (285 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_285_suffix_zero :
    (∑ x ∈ Finset.range 140,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (285 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_285 :
    recurrence5LeadingSquare.coeff 285 =
      (((156009735697946 * 10 ^ 70 +
        5859936735077810798033703171540109270773300315259257631512984601033094) * 10 ^ 70 +
        5265845704522620634495155436578680192471931731668793139634336490809478) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 286 = 140 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 6 +
      140 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_285_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_285_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_286_prefix_zero :
    (∑ x ∈ Finset.range 141,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (286 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (286 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_286_suffix_zero :
    (∑ x ∈ Finset.range 141,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (286 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_286 :
    recurrence5LeadingSquare.coeff 286 =
      (((2035062090 * 10 ^ 70 +
        0179960113782870631690268433697773097135546163968289082306967743957749) * 10 ^ 70 +
        3144170084976513105969801665408604428075030123179798529527509233607175) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 287 = 141 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 5 +
      141 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_286_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_286_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_287_prefix_zero :
    (∑ x ∈ Finset.range 142,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (287 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (287 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_287_suffix_zero :
    (∑ x ∈ Finset.range 142,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (287 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_287 :
    recurrence5LeadingSquare.coeff 287 =
      (((6485 * 10 ^ 70 +
        1710378035870775278233602911869159809917446938353731592273647049537588) * 10 ^ 70 +
        3600204979958938962772125405667954595778180933696458330412809963439284) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 288 = 142 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 4 +
      142 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_287_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_287_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_288_prefix_zero :
    (∑ x ∈ Finset.range 143,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (288 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (288 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_288_suffix_zero :
    (∑ x ∈ Finset.range 143,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (288 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_288 :
    recurrence5LeadingSquare.coeff 288 =
      ((64206943109623469248699862684895021001655272932121046817495043511079 * 10 ^ 70 +
        1831079368786943781040069612821648930085162844970677760233734908351495) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 289 = 143 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 3 +
      143 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_288_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_288_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_289_prefix_zero :
    (∑ x ∈ Finset.range 144,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (289 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (289 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_289_suffix_zero :
    (∑ x ∈ Finset.range 144,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (289 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_289 :
    recurrence5LeadingSquare.coeff 289 =
      ((8299577450460314594916163985198105897840730771908019315171300 * 10 ^ 70 +
        4155436416422783129931816374780594951583757863994521018233855751665394) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 290 = 144 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 2 +
      144 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_289_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_289_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_290_prefix_zero :
    (∑ x ∈ Finset.range 145,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (290 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (290 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_290_suffix_zero :
    (∑ x ∈ Finset.range 145,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (290 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_290 :
    recurrence5LeadingSquare.coeff 290 =
      ((288387762078554381313340337703578897586805980207507208 * 10 ^ 70 +
        3832674952841979578263788122504638932762612571665016111438034953793249) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 291 = 145 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 1 +
      145 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_290_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_290_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
