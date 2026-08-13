/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupB2
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupLeadingSquarePart0Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 5 lookup certificate: LeadingSquare coefficient convolution

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/
public section
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

private theorem recurrence5LeadingSquare_coeff_160_prefix_zero :
    (∑ x ∈ Finset.range 15,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (160 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (160 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_160_suffix_zero :
    (∑ x ∈ Finset.range 15,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (160 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_160 :
    recurrence5LeadingSquare.coeff 160 =
      ((((6425423949230125903648932755058402145995 * 10 ^ 70 +
        9107689134863497149107474569475567152853703572552493817787060892285439) * 10 ^ 70 +
        9692111443874336568255908785417525571781788632011298400222528559446048) * 10 ^ 70 +
        1695695409855846280838571107239351117568182830899353138785888339600283) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 161 = 15 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
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
    rw [show 18 = 3 +
      15 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_160_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_160_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_161_prefix_zero :
    (∑ x ∈ Finset.range 16,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (161 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (161 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_161_suffix_zero :
    (∑ x ∈ Finset.range 16,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (161 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_161 :
    recurrence5LeadingSquare.coeff 161 =
      -((((4439165227384909395979681134310705614880 * 10 ^ 70 +
        4305518400676501655120854169873749122118460943762696606220395489244005) * 10 ^ 70 +
        6077159183509387126332448532244942720789745414191976429761236269844895) * 10 ^ 70 +
        7089561195275130943645016035595296673120443086303513342375978672454898) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 162 = 16 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
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
    rw [show 18 = 2 +
      16 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_161_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_161_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_162_prefix_zero :
    (∑ x ∈ Finset.range 17,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (162 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (162 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_162_suffix_zero :
    (∑ x ∈ Finset.range 17,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (162 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_162 :
    recurrence5LeadingSquare.coeff 162 =
      ((((2862948418876506653745801788398143558801 * 10 ^ 70 +
        4342033863230452447010339467086881086871772187631164157894624294651610) * 10 ^ 70 +
        6707406225299143557962287302084188272027718352585289411543086819439856) * 10 ^ 70 +
        1104597810074096565192150631021927996120120782134180574478000319646749) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 163 = 17 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
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
    rw [show 18 = 1 +
      17 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_162_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_162_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_163_prefix_zero :
    (∑ x ∈ Finset.range 18,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (163 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (163 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_163_suffix_zero :
    (∑ x ∈ Finset.range 18,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (163 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_163 :
    recurrence5LeadingSquare.coeff 163 =
      -((((1718760669647621934457635887627495546826 * 10 ^ 70 +
        8010589723365189467712662890660231554153914974349373823223014157220859) * 10 ^ 70 +
        6826436096434461271121827639866567359541582514959621843922423633577687) * 10 ^ 70 +
        6620390704950750829584628062835901831109739496861602322838592626174502) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 164 = 18 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_163_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_163_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_164_prefix_zero :
    (∑ x ∈ Finset.range 19,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (164 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (164 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_164_suffix_zero :
    (∑ x ∈ Finset.range 19,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (164 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_164 :
    recurrence5LeadingSquare.coeff 164 =
      ((((950360649181440196787856212102513960515 * 10 ^ 70 +
        4922588523308735299202125901044942987429895923875629863193172503236119) * 10 ^ 70 +
        7235924378117600869187492313142522813413437286979279745567607607703625) * 10 ^ 70 +
        3529559605903812383817924124833149140331345148400672705753696155551413) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 165 = 19 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 31 +
      19 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_164_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_164_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_165_prefix_zero :
    (∑ x ∈ Finset.range 20,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (165 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (165 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_165_suffix_zero :
    (∑ x ∈ Finset.range 20,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (165 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_165 :
    recurrence5LeadingSquare.coeff 165 =
      -((((472185808235271262756186925677547502532 * 10 ^ 70 +
        0988094917608214506573925474935877886002906680141254573053614710149737) * 10 ^ 70 +
        7229153200723636308385539327574348138592983570809082928468330711985373) * 10 ^ 70 +
        1024940422331961560406631149698721425176699147531766941869453546405162) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 166 = 20 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 30 +
      20 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_165_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_165_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_166_prefix_zero :
    (∑ x ∈ Finset.range 21,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (166 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (166 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_166_suffix_zero :
    (∑ x ∈ Finset.range 21,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (166 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_166 :
    recurrence5LeadingSquare.coeff 166 =
      ((((198473809856514260977179898504399251642 * 10 ^ 70 +
        4664221899172317483702543756774539866296343774917064591659377727214819) * 10 ^ 70 +
        5047820751052134299293664638875141825523225726188791213640090518221088) * 10 ^ 70 +
        9470103012563412811990731853576447100913699281602289306409050182252917) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 167 = 21 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 29 +
      21 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_166_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_166_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_167_prefix_zero :
    (∑ x ∈ Finset.range 22,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (167 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (167 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_167_suffix_zero :
    (∑ x ∈ Finset.range 22,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (167 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_167 :
    recurrence5LeadingSquare.coeff 167 =
      -((((57348314656454286510136904001766476954 * 10 ^ 70 +
        7635818327874081938885181900985866615462079902096739492506268553936779) * 10 ^ 70 +
        9347618081347566440576935883778225740629175710423182891998190751387076) * 10 ^ 70 +
        1203163290567526117717258243248490922452043623183140855475767942977572) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 168 = 22 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 28 +
      22 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_167_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_167_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_168_prefix_zero :
    (∑ x ∈ Finset.range 23,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (168 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (168 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_168_suffix_zero :
    (∑ x ∈ Finset.range 23,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (168 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_168 :
    recurrence5LeadingSquare.coeff 168 =
      -((((4850875657633937525174223265274474112 * 10 ^ 70 +
        3661885233440753027850648712825927221966809664198476881890906254842307) * 10 ^ 70 +
        4533014456819735322424291187878816535135525148758918899487301630641325) * 10 ^ 70 +
        7273880548539815923683969208289868478661582884344339164704785869331003) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 169 = 23 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 27 +
      23 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_168_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_168_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_169_prefix_zero :
    (∑ x ∈ Finset.range 24,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (169 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (169 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_169_suffix_zero :
    (∑ x ∈ Finset.range 24,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (169 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_169 :
    recurrence5LeadingSquare.coeff 169 =
      ((((24615942181231766299028633526388173920 * 10 ^ 70 +
        9561176326598032389717625834784555820885938745271096265097369547749113) * 10 ^ 70 +
        3541754712078090031101573963006337363666933311634486150377849289219076) * 10 ^ 70 +
        9861906952212343740275334104439705744005616834237670203744920524348488) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 170 = 24 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 26 +
      24 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_169_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_169_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_170_prefix_zero :
    (∑ x ∈ Finset.range 25,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (170 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (170 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_170_suffix_zero :
    (∑ x ∈ Finset.range 25,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (170 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_170 :
    recurrence5LeadingSquare.coeff 170 =
      -((((24647256487682943410519813583641724372 * 10 ^ 70 +
        1111040886867031015905937880231415460607001789474983736284642829085845) * 10 ^ 70 +
        9806290932125339572595383447102674766996408875649768634767002196825975) * 10 ^ 70 +
        9175458875277999246537784248988738926649355122780990078619021555532972) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 171 = 25 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 25 +
      25 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_170_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_170_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_171_prefix_zero :
    (∑ x ∈ Finset.range 26,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (171 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (171 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_171_suffix_zero :
    (∑ x ∈ Finset.range 26,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (171 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_171 :
    recurrence5LeadingSquare.coeff 171 =
      ((((17723699993655050235792702262561538657 * 10 ^ 70 +
        2422709063100780003144839402528979125599548729391550640337406032380337) * 10 ^ 70 +
        2789388522391368185123376393371781940632992389093782968735470102228561) * 10 ^ 70 +
        1743229797830557100652799772065644868162926124911655020653810528872274) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 172 = 26 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 24 +
      26 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_171_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_171_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_172_prefix_zero :
    (∑ x ∈ Finset.range 27,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (172 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (172 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_172_suffix_zero :
    (∑ x ∈ Finset.range 27,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (172 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_172 :
    recurrence5LeadingSquare.coeff 172 =
      -((((10136771069821366023074794745634793513 * 10 ^ 70 +
        5443428216379032827218174770543859577710606924683670152865447569029513) * 10 ^ 70 +
        3639660650627585271536311273721521695590355069527122567961039597957641) * 10 ^ 70 +
        6798693109361303826513180862217053931991634917379503490626532955536119) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 173 = 27 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 23 +
      27 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_172_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_172_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_173_prefix_zero :
    (∑ x ∈ Finset.range 28,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (173 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (173 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_173_suffix_zero :
    (∑ x ∈ Finset.range 28,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (173 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_173 :
    recurrence5LeadingSquare.coeff 173 =
      ((((4337847301530408592354699196359107953 * 10 ^ 70 +
        6769084747528890704401761030870446837386104295742300863825961385452838) * 10 ^ 70 +
        4984119648767122936746765772398155789943809095884195316789890933222975) * 10 ^ 70 +
        8066341704349482871163850270409758540159506919102501152740603555633830) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 174 = 28 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 22 +
      28 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_173_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_173_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_174_prefix_zero :
    (∑ x ∈ Finset.range 29,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (174 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (174 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_174_suffix_zero :
    (∑ x ∈ Finset.range 29,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (174 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_174 :
    recurrence5LeadingSquare.coeff 174 =
      -((((772501120042886170381660363928076186 * 10 ^ 70 +
        7033381953269621392031931799538442093595975730160531758533088811658295) * 10 ^ 70 +
        6093341422210669211651973145106379831170017344382360881639973671719575) * 10 ^ 70 +
        0917239562732953543710203152307014276464243152038167645578757776469335) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 175 = 29 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 21 +
      29 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_174_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_174_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_175_prefix_zero :
    (∑ x ∈ Finset.range 30,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (175 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (175 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_175_suffix_zero :
    (∑ x ∈ Finset.range 30,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (175 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_175 :
    recurrence5LeadingSquare.coeff 175 =
      -((((971586699118649096533545109847260902 * 10 ^ 70 +
        7247387351601115832200636951463816346319223483864751683129026636786115) * 10 ^ 70 +
        5555701086910947793832710380306527883253768686527126024821765346456457) * 10 ^ 70 +
        6096273620797176604049789593774549946380982625488903490368168588952876) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 176 = 30 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 20 +
      30 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_175_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_175_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_176_prefix_zero :
    (∑ x ∈ Finset.range 31,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (176 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (176 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_176_suffix_zero :
    (∑ x ∈ Finset.range 31,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (176 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_176 :
    recurrence5LeadingSquare.coeff 176 =
      ((((1527084401301375530812756696332130064 * 10 ^ 70 +
        7165409391883242628920857401336100436389924952632070968389870348643091) * 10 ^ 70 +
        4741987304383025039222702276706531217681563622772267367260186084831545) * 10 ^ 70 +
        3487430522570172171158383404427286751508510317942296675439722981980879) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 177 = 31 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 19 +
      31 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_176_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_176_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_177_prefix_zero :
    (∑ x ∈ Finset.range 32,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (177 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (177 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_177_suffix_zero :
    (∑ x ∈ Finset.range 32,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (177 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_177 :
    recurrence5LeadingSquare.coeff 177 =
      -((((1449794278216691863206650677442525486 * 10 ^ 70 +
        1755825257447273795969817556793885648245126127830486568632214670525352) * 10 ^ 70 +
        8686466292939333499053130658846037868278792193167565833312307578357528) * 10 ^ 70 +
        4974187613406874241846333192644480624735359556392183766044137517477004) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 178 = 32 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 18 +
      32 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_177_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_177_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_178_prefix_zero :
    (∑ x ∈ Finset.range 33,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (178 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (178 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_178_suffix_zero :
    (∑ x ∈ Finset.range 33,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (178 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_178 :
    recurrence5LeadingSquare.coeff 178 =
      ((((1123123947603098363254553577225348750 * 10 ^ 70 +
        5519246331098613678920585601862659273095777067364448702800470929307197) * 10 ^ 70 +
        0632373757505121453589629101136792795864568457899393004367174919760126) * 10 ^ 70 +
        7795760738909128126333830361997867966544183035428770420967691888760616) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 179 = 33 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 17 +
      33 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_178_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_178_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_179_prefix_zero :
    (∑ x ∈ Finset.range 34,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (179 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (179 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_179_suffix_zero :
    (∑ x ∈ Finset.range 34,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (179 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_179 :
    recurrence5LeadingSquare.coeff 179 =
      -((((764495114649890410957690948906132155 * 10 ^ 70 +
        4113204358121422032546275255887848955746926390718993983937963880804406) * 10 ^ 70 +
        7924773051677050131734033525006201510919380757869296223071534313767912) * 10 ^ 70 +
        4502380407099773523545544399637704346797796373518315887734878763299960) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 180 = 34 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 16 +
      34 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_179_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_179_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_180_prefix_zero :
    (∑ x ∈ Finset.range 35,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (180 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (180 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_180_suffix_zero :
    (∑ x ∈ Finset.range 35,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (180 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_180 :
    recurrence5LeadingSquare.coeff 180 =
      ((((470240981518705010352951422111349966 * 10 ^ 70 +
        4195325043993749746927302253358838779840727075232260761594831597735088) * 10 ^ 70 +
        9936872674722504249308553894983483162970436495133542600197117576890675) * 10 ^ 70 +
        3451823172165493800332335695638856520070621007843943167646564419812948) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 181 = 35 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 15 +
      35 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_180_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_180_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_181_prefix_zero :
    (∑ x ∈ Finset.range 36,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (181 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (181 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_181_suffix_zero :
    (∑ x ∈ Finset.range 36,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (181 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_181 :
    recurrence5LeadingSquare.coeff 181 =
      -((((264329563572976696963147303246285676 * 10 ^ 70 +
        8123569060404396708844396919642970846779238537128699460264242951530834) * 10 ^ 70 +
        2086593299171644101847355594512204553922942053249266422709049112777511) * 10 ^ 70 +
        0891619002008047795728002564328133279047363764795413330748531375361494) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 182 = 36 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 14 +
      36 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_181_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_181_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_182_prefix_zero :
    (∑ x ∈ Finset.range 37,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (182 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (182 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_182_suffix_zero :
    (∑ x ∈ Finset.range 37,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (182 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_182 :
    recurrence5LeadingSquare.coeff 182 =
      ((((136094685096977444854166396467567873 * 10 ^ 70 +
        6115575661953175521698109038307176765239539961016235293763834271492079) * 10 ^ 70 +
        4122839101605423350098952092997367887833479199314167013152312074639062) * 10 ^ 70 +
        8475245818269039747663641128604509013762952199817834129477970362397775) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 183 = 37 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 13 +
      37 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_182_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_182_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_183_prefix_zero :
    (∑ x ∈ Finset.range 38,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (183 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (183 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_183_suffix_zero :
    (∑ x ∈ Finset.range 38,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (183 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_183 :
    recurrence5LeadingSquare.coeff 183 =
      -((((63868093960684847454282813095694700 * 10 ^ 70 +
        4397053136926962208643106089697223298995707036462979393509930588388571) * 10 ^ 70 +
        2093101928877046340501684548125957689274299748555280011306530787929242) * 10 ^ 70 +
        4909790030153828021272485981672953897513694813127827871761808744980768) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 184 = 38 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 12 +
      38 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_183_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_183_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_184_prefix_zero :
    (∑ x ∈ Finset.range 39,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (184 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (184 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_184_suffix_zero :
    (∑ x ∈ Finset.range 39,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (184 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_184 :
    recurrence5LeadingSquare.coeff 184 =
      ((((26945838065508253792564806073219029 * 10 ^ 70 +
        5561008263949047550841438856291961932595339515462800613769412953949822) * 10 ^ 70 +
        9714171260973356925688032651557874633748403025531513092972643466945980) * 10 ^ 70 +
        4554749183260100408068992549168305880333192115880746955349797618333052) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 185 = 39 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 11 +
      39 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_184_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_184_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_185_prefix_zero :
    (∑ x ∈ Finset.range 40,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (185 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (185 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_185_suffix_zero :
    (∑ x ∈ Finset.range 40,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (185 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_185 :
    recurrence5LeadingSquare.coeff 185 =
      -((((9919408325809655371983712446302507 * 10 ^ 70 +
        3098056648336627284983651009600198545955780441747063762290043158737618) * 10 ^ 70 +
        6505388120873342234367750058959592504618518071433468827664640147408410) * 10 ^ 70 +
        3861636299944094868397022411197130988548070871260037334287272277637800) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 186 = 40 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 10 +
      40 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_185_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_185_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_186_prefix_zero :
    (∑ x ∈ Finset.range 41,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (186 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (186 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_186_suffix_zero :
    (∑ x ∈ Finset.range 41,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (186 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_186 :
    recurrence5LeadingSquare.coeff 186 =
      ((((2967448466249035428556383489000030 * 10 ^ 70 +
        5188162915108352378794413492229904467090873386884842174139402114581264) * 10 ^ 70 +
        0005503229074058779638023591381437701088270798720012862172136849110554) * 10 ^ 70 +
        2905538545933122631318885923117277407730732967089871148836053253452339) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 187 = 41 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 9 +
      41 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_186_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_186_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_187_prefix_zero :
    (∑ x ∈ Finset.range 42,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (187 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (187 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_187_suffix_zero :
    (∑ x ∈ Finset.range 42,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (187 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_187 :
    recurrence5LeadingSquare.coeff 187 =
      -((((563156535326957223376422444119698 * 10 ^ 70 +
        0397985797411772127885081147308318211148351617090766281018658582266438) * 10 ^ 70 +
        4034463789857273957313605882886127629991564967811390066885978346157137) * 10 ^ 70 +
        2949162906072418599531817932887482913151126633070603884387941886157710) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 188 = 42 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 8 +
      42 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_187_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_187_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
