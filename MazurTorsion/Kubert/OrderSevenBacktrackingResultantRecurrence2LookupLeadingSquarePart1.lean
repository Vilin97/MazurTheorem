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

private theorem recurrence2LeadingSquare_coeff_224_prefix_zero :
    (∑ x ∈ Finset.range 90,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (224 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (224 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_224_suffix_zero :
    (∑ x ∈ Finset.range 90,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (224 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_224 :
    recurrence2LeadingSquare.coeff 224 =
      ((561809761417290135585358064070334009503682424858883366562967118721 * 10 ^ 70 +
        1267377411830800253673091633820916822465455485082650459395233447406406) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 225 = 90 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 13 +
      90 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_224_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_224_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_225_prefix_zero :
    (∑ x ∈ Finset.range 91,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (225 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (225 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_225_suffix_zero :
    (∑ x ∈ Finset.range 91,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (225 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_225 :
    recurrence2LeadingSquare.coeff 225 =
      -((58621623113470959536612563423384900819108175116212178194759299991 * 10 ^ 70 +
        3197270855949458407654059225323685398018341953685335948671800447565622) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 226 = 91 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 12 +
      91 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_225_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_225_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_226_prefix_zero :
    (∑ x ∈ Finset.range 92,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (226 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (226 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_226_suffix_zero :
    (∑ x ∈ Finset.range 92,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (226 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_226 :
    recurrence2LeadingSquare.coeff 226 =
      ((5654646791334891163180811991514835722586150645529370525005555025 * 10 ^ 70 +
        2491592221681213210366656829801459736634745809782604066972868749535703) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 227 = 92 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 11 +
      92 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_226_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_226_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_227_prefix_zero :
    (∑ x ∈ Finset.range 93,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (227 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (227 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_227_suffix_zero :
    (∑ x ∈ Finset.range 93,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (227 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_227 :
    recurrence2LeadingSquare.coeff 227 =
      -((502207919304935493863026772744868723576554329361824668685097198 * 10 ^ 70 +
        0822628446767478857412598553183753164533565300883454632656896928795302) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 228 = 93 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 10 +
      93 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_227_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_227_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_228_prefix_zero :
    (∑ x ∈ Finset.range 94,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (228 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (228 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_228_suffix_zero :
    (∑ x ∈ Finset.range 94,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (228 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_228 :
    recurrence2LeadingSquare.coeff 228 =
      ((40883739372899976403995774669750458666500107055294971252843718 * 10 ^ 70 +
        0664152813445048736941894973947984780808800372330968267677582210847135) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 229 = 94 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 9 +
      94 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_228_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_228_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_229_prefix_zero :
    (∑ x ∈ Finset.range 95,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (229 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (229 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_229_suffix_zero :
    (∑ x ∈ Finset.range 95,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (229 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_229 :
    recurrence2LeadingSquare.coeff 229 =
      -((3035582872312280507228906623488125720153601986813114188170157 * 10 ^ 70 +
        3958663405679618182530702662017700522250678284193957694181787567129962) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 230 = 95 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 8 +
      95 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_229_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_229_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_230_prefix_zero :
    (∑ x ∈ Finset.range 96,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (230 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (230 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_230_suffix_zero :
    (∑ x ∈ Finset.range 96,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (230 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_230 :
    recurrence2LeadingSquare.coeff 230 =
      ((204424673581056177391562605993804808697109917032794883958632 * 10 ^ 70 +
        3758243883643324923171703834851926241130962816797219578946957694898028) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 231 = 96 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 7 +
      96 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_230_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_230_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_231_prefix_zero :
    (∑ x ∈ Finset.range 97,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (231 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (231 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_231_suffix_zero :
    (∑ x ∈ Finset.range 97,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (231 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_231 :
    recurrence2LeadingSquare.coeff 231 =
      -((12407761274524548054352292238204188663599817398960623863107 * 10 ^ 70 +
        3025200631630691693146437794988718298630907170333069859018963093026134) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 232 = 97 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 6 +
      97 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_231_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_231_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_232_prefix_zero :
    (∑ x ∈ Finset.range 98,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (232 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (232 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_232_suffix_zero :
    (∑ x ∈ Finset.range 98,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (232 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_232 :
    recurrence2LeadingSquare.coeff 232 =
      ((673949085123631859268691057639288307199633637829206666572 * 10 ^ 70 +
        6766371887717385774749830915345929390722328417180227789644426962474733) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 233 = 98 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 5 +
      98 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_232_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_232_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_233_prefix_zero :
    (∑ x ∈ Finset.range 99,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (233 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (233 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_233_suffix_zero :
    (∑ x ∈ Finset.range 99,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (233 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_233 :
    recurrence2LeadingSquare.coeff 233 =
      -((32493634160801342122221232307759319455763996340018635774 * 10 ^ 70 +
        8470577107644099678023432405205586602852606796341490454120780639539430) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 234 = 99 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 4 +
      99 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_233_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_233_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_234_prefix_zero :
    (∑ x ∈ Finset.range 100,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (234 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (234 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_234_suffix_zero :
    (∑ x ∈ Finset.range 100,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (234 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_234 :
    recurrence2LeadingSquare.coeff 234 =
      ((1377613349505456866723128077963437619444679401495324239 * 10 ^ 70 +
        3446104712093439741472727877315406591206950008178631536995663760485137) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 235 = 100 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 3 +
      100 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_234_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_234_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_235_prefix_zero :
    (∑ x ∈ Finset.range 101,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (235 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (235 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_235_suffix_zero :
    (∑ x ∈ Finset.range 101,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (235 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_235 :
    recurrence2LeadingSquare.coeff 235 =
      -((50797767058235850070711144865158715419542093118985747 * 10 ^ 70 +
        9852866194208145312475868768133488072083669622620587881257886429645868) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 236 = 101 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 2 +
      101 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_235_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_235_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_236_prefix_zero :
    (∑ x ∈ Finset.range 102,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (236 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (236 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_236_suffix_zero :
    (∑ x ∈ Finset.range 102,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (236 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_236 :
    recurrence2LeadingSquare.coeff 236 =
      ((1607939379379968372478556430804934177003922969514504 * 10 ^ 70 +
        5514152136087890738958755552199277499913799747722077762257412080548610) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 237 = 102 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 1 +
      102 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_236_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_236_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_237_prefix_zero :
    (∑ x ∈ Finset.range 103,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (237 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (237 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_237_suffix_zero :
    (∑ x ∈ Finset.range 103,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (237 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_237 :
    recurrence2LeadingSquare.coeff 237 =
      -((42998253372772890541051360049826234760646013855082 * 10 ^ 70 +
        7632709854350945714703022698913843338005919241534085204893813772233260) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 238 = 103 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_237_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_237_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_238_prefix_zero :
    (∑ x ∈ Finset.range 104,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (238 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (238 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_238_suffix_zero :
    (∑ x ∈ Finset.range 104,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (238 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_238 :
    recurrence2LeadingSquare.coeff 238 =
      ((951737838638004543567181235992893153489967863312 * 10 ^ 70 +
        0588330584551406139297989269195952025204045562199404816492024931085286) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 239 = 104 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 31 +
      104 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_238_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_238_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_239_prefix_zero :
    (∑ x ∈ Finset.range 105,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (239 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (239 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_239_suffix_zero :
    (∑ x ∈ Finset.range 105,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (239 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_239 :
    recurrence2LeadingSquare.coeff 239 =
      -((16957553185211324559971225701742983204324775162 * 10 ^ 70 +
        8509603758573789201180414536420787025003982038878748953570464949274184) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 240 = 105 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 30 +
      105 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_239_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_239_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_240_prefix_zero :
    (∑ x ∈ Finset.range 106,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (240 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (240 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_240_suffix_zero :
    (∑ x ∈ Finset.range 106,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (240 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_240 :
    recurrence2LeadingSquare.coeff 240 =
      ((233073908422455085885065242601835263197905841 * 10 ^ 70 +
        5557421957841954438792747917135043257204218186215064161969879921821024) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 241 = 106 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 29 +
      106 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_240_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_240_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_241_prefix_zero :
    (∑ x ∈ Finset.range 107,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (241 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (241 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_241_suffix_zero :
    (∑ x ∈ Finset.range 107,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (241 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_241 :
    recurrence2LeadingSquare.coeff 241 =
      -((2282135561078593235068932087932267857111489 * 10 ^ 70 +
        2913425173114419360017600604440949819545123610837435414138138203325562) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 242 = 107 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 28 +
      107 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_241_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_241_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_242_prefix_zero :
    (∑ x ∈ Finset.range 108,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (242 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (242 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_242_suffix_zero :
    (∑ x ∈ Finset.range 108,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (242 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_242 :
    recurrence2LeadingSquare.coeff 242 =
      ((12699925842094552641005027792615968774784 * 10 ^ 70 +
        5087779474356342071759153966331467126075117820082403826268289462191408) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 243 = 108 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 27 +
      108 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_242_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_242_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_243_prefix_zero :
    (∑ x ∈ Finset.range 109,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (243 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (243 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_243_suffix_zero :
    (∑ x ∈ Finset.range 109,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (243 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_243 :
    recurrence2LeadingSquare.coeff 243 =
      ((13235890497248962405078804334327787549 * 10 ^ 70 +
        0717196278864211425241316528067562875156847300900824522712498960513128) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 244 = 109 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 26 +
      109 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_243_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_243_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_244_prefix_zero :
    (∑ x ∈ Finset.range 110,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (244 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (244 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_244_suffix_zero :
    (∑ x ∈ Finset.range 110,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (244 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_244 :
    recurrence2LeadingSquare.coeff 244 =
      -((888769690578224965769577527148145705 * 10 ^ 70 +
        6311908186118668759169709388210241262529946510078530934931949249777165) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 245 = 110 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 25 +
      110 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_244_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_244_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_245_prefix_zero :
    (∑ x ∈ Finset.range 111,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (245 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (245 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_245_suffix_zero :
    (∑ x ∈ Finset.range 111,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (245 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_245 :
    recurrence2LeadingSquare.coeff 245 =
      ((6591183252195620445529857283924621 * 10 ^ 70 +
        8578087086772039376704652641030212680884041868381979789802844040734890) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 246 = 111 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 24 +
      111 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_245_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_245_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_246_prefix_zero :
    (∑ x ∈ Finset.range 112,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (246 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (246 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_246_suffix_zero :
    (∑ x ∈ Finset.range 112,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (246 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_246 :
    recurrence2LeadingSquare.coeff 246 =
      -((9521708187634297077491647703786 * 10 ^ 70 +
        5773407055877061872535422247793287096207382579842969357394317568201231) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 247 = 112 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 23 +
      112 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_246_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_246_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_247_prefix_zero :
    (∑ x ∈ Finset.range 113,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (247 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (247 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_247_suffix_zero :
    (∑ x ∈ Finset.range 113,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (247 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_247 :
    recurrence2LeadingSquare.coeff 247 =
      -((152199368632941720907287026288 * 10 ^ 70 +
        9470528690200840531886874799841826828362247016558448088545204199023660) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 248 = 113 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 22 +
      113 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_247_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_247_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_248_prefix_zero :
    (∑ x ∈ Finset.range 114,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (248 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (248 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_248_suffix_zero :
    (∑ x ∈ Finset.range 114,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (248 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_248 :
    recurrence2LeadingSquare.coeff 248 =
      ((951179927042320541491367718 * 10 ^ 70 +
        7099706315522876211007602325259702763961639317047489799315109691621596) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 249 = 114 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 21 +
      114 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_248_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_248_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_249_prefix_zero :
    (∑ x ∈ Finset.range 115,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (249 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (249 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_249_suffix_zero :
    (∑ x ∈ Finset.range 115,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (249 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_249 :
    recurrence2LeadingSquare.coeff 249 =
      -((913805482927709469001513 * 10 ^ 70 +
        1501946789877945668389565758428867107594273305538065689946904345952682) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 250 = 115 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 20 +
      115 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_249_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_249_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_250_prefix_zero :
    (∑ x ∈ Finset.range 116,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (250 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (250 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_250_suffix_zero :
    (∑ x ∈ Finset.range 116,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (250 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_250 :
    recurrence2LeadingSquare.coeff 250 =
      -((11043535116429383580879 * 10 ^ 70 +
        7211188543246020734587759503637895002172724101780653086701682714544867) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 251 = 116 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 19 +
      116 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_250_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_250_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_251_prefix_zero :
    (∑ x ∈ Finset.range 117,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (251 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (251 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_251_suffix_zero :
    (∑ x ∈ Finset.range 117,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (251 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_251 :
    recurrence2LeadingSquare.coeff 251 =
      ((46241981649816768616 * 10 ^ 70 +
        6666445979314224947688883614767358061767643910388377365494886630608028) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 252 = 117 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 18 +
      117 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_251_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_251_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_252_prefix_zero :
    (∑ x ∈ Finset.range 118,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (252 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (252 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_252_suffix_zero :
    (∑ x ∈ Finset.range 118,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (252 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_252 :
    recurrence2LeadingSquare.coeff 252 =
      -((39179208295356993 * 10 ^ 70 +
        0955145394499404501391588489566709785373118435050329670701696836374851) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 253 = 118 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 17 +
      118 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_252_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_252_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_253_prefix_zero :
    (∑ x ∈ Finset.range 119,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (253 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (253 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_253_suffix_zero :
    (∑ x ∈ Finset.range 119,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (253 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_253 :
    recurrence2LeadingSquare.coeff 253 =
      -((205358698960284 * 10 ^ 70 +
        4886539382272811185449248981975309840420720554500193118218364382619158) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 254 = 119 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 16 +
      119 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_253_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_253_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_254_prefix_zero :
    (∑ x ∈ Finset.range 120,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (254 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (254 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_254_suffix_zero :
    (∑ x ∈ Finset.range 120,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (254 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_254 :
    recurrence2LeadingSquare.coeff 254 =
      ((762979121991 * 10 ^ 70 +
        2376339231357296252793618506141108963497373477934851059795916552708738) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 255 = 120 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 15 +
      120 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_254_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_254_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_255_prefix_zero :
    (∑ x ∈ Finset.range 121,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (255 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (255 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_255_suffix_zero :
    (∑ x ∈ Finset.range 121,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (255 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_255 :
    recurrence2LeadingSquare.coeff 255 =
      -((1252542529 * 10 ^ 70 +
        2855645366157441560821791846063742747170387688567707668819919351475680) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 256 = 121 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 14 +
      121 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_255_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_255_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_256_prefix_zero :
    (∑ x ∈ Finset.range 122,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (256 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (256 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_256_suffix_zero :
    (∑ x ∈ Finset.range 122,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (256 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_256 :
    recurrence2LeadingSquare.coeff 256 =
      ((1190390 * 10 ^ 70 +
        5668669804374762879023083911000695840052534576183597927143988184916627) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 257 = 122 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 13 +
      122 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_256_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_256_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_257_prefix_zero :
    (∑ x ∈ Finset.range 123,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (257 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (257 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_257_suffix_zero :
    (∑ x ∈ Finset.range 123,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (257 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_257 :
    recurrence2LeadingSquare.coeff 257 =
      -((686 * 10 ^ 70 +
        7129352649463879045477947982222711245069047553500365887609327273800266) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 258 = 123 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 12 +
      123 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_257_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_257_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_258_prefix_zero :
    (∑ x ∈ Finset.range 124,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (258 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (258 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_258_suffix_zero :
    (∑ x ∈ Finset.range 124,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (258 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_258 :
    recurrence2LeadingSquare.coeff 258 =
      (2385711292812592668185321574152758713260339832977141265159278262127015 : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 259 = 124 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 11 +
      124 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_258_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_258_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_259_prefix_zero :
    (∑ x ∈ Finset.range 125,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (259 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (259 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_259_suffix_zero :
    (∑ x ∈ Finset.range 125,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (259 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_259 :
    recurrence2LeadingSquare.coeff 259 =
      (-481872277519030416031028333064414110199545218781126383778227319502 : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 260 = 125 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 10 +
      125 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_259_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_259_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_260_prefix_zero :
    (∑ x ∈ Finset.range 126,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (260 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (260 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_260_suffix_zero :
    (∑ x ∈ Finset.range 126,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (260 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_260 :
    recurrence2LeadingSquare.coeff 260 =
      (53841771322926348327685386648171838138229482693893494721410789 : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 261 = 126 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 9 +
      126 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_260_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_260_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_261_prefix_zero :
    (∑ x ∈ Finset.range 127,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (261 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (261 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_261_suffix_zero :
    (∑ x ∈ Finset.range 127,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (261 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_261 :
    recurrence2LeadingSquare.coeff 261 =
      (-3092793674963169611298319377989159470325820478404925031202 : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 262 = 127 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 8 +
      127 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_261_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_261_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_262_prefix_zero :
    (∑ x ∈ Finset.range 128,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (262 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (262 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_262_suffix_zero :
    (∑ x ∈ Finset.range 128,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (262 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_262 :
    recurrence2LeadingSquare.coeff 262 =
      (85062553733218251738974939428507320800293573276860431 : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 263 = 128 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 7 +
      128 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_262_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_262_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_263_prefix_zero :
    (∑ x ∈ Finset.range 129,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (263 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (263 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_263_suffix_zero :
    (∑ x ∈ Finset.range 129,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (263 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_263 :
    recurrence2LeadingSquare.coeff 263 =
      (-971429686168595293080674931260101722348428922526 : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 264 = 129 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 6 +
      129 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_263_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_263_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_264_prefix_zero :
    (∑ x ∈ Finset.range 130,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (264 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (264 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_264_suffix_zero :
    (∑ x ∈ Finset.range 130,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (264 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_264 :
    recurrence2LeadingSquare.coeff 264 =
      (4339432442551415782594727081480877152045890 : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 265 = 130 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 5 +
      130 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_264_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_264_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_265_prefix_zero :
    (∑ x ∈ Finset.range 131,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (265 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (265 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_265_suffix_zero :
    (∑ x ∈ Finset.range 131,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (265 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_265 :
    recurrence2LeadingSquare.coeff 265 =
      (-5221574427476610763264270701221703918 : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 266 = 131 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 4 +
      131 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_265_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_265_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_266_prefix_zero :
    (∑ x ∈ Finset.range 132,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (266 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (266 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_266_suffix_zero :
    (∑ x ∈ Finset.range 132,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (266 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_266 :
    recurrence2LeadingSquare.coeff 266 =
      (1895399483217394147509375939816 : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 267 = 132 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 3 +
      132 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_266_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_266_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_267_prefix_zero :
    (∑ x ∈ Finset.range 133,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (267 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (267 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_267_suffix_zero :
    (∑ x ∈ Finset.range 133,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (267 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_267 :
    recurrence2LeadingSquare.coeff 267 =
      (-25231363388779055119656 : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 268 = 133 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 2 +
      133 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_267_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_267_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2LeadingSquare_coeff_268_prefix_zero :
    (∑ x ∈ Finset.range 134,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (268 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (268 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_268_suffix_zero :
    (∑ x ∈ Finset.range 134,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (268 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_268 :
    recurrence2LeadingSquare.coeff 268 =
      (85566736552441 : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 269 = 134 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 1 +
      134 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_268_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_268_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
