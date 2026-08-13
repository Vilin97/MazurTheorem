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

private theorem recurrence5LeadingSquare_coeff_188_prefix_zero :
    (∑ x ∈ Finset.range 43,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (188 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (188 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_188_suffix_zero :
    (∑ x ∈ Finset.range 43,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (188 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_188 :
    recurrence5LeadingSquare.coeff 188 =
      -((((57305697164852468745897396574251 * 10 ^ 70 +
        8536540842346309279154144086400067772278270501772690953446170442796367) * 10 ^ 70 +
        9381810029238834776882118635213418195635582994435229187214962529635630) * 10 ^ 70 +
        9829441148395651582962173443193867135649412017262941482196052300131110) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 189 = 43 +
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
    rw [show 50 = 7 +
      43 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_188_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_188_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_189_prefix_zero :
    (∑ x ∈ Finset.range 44,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (189 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (189 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_189_suffix_zero :
    (∑ x ∈ Finset.range 44,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (189 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_189 :
    recurrence5LeadingSquare.coeff 189 =
      ((((109415433767492921484401829492976 * 10 ^ 70 +
        9466003016425338174055725158692667301088852439514267675406443471478551) * 10 ^ 70 +
        3762558631473380099234593513848349489246460766761713170293094921588577) * 10 ^ 70 +
        8280722152329515743525974277388666828046091196961963589959322921071648) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 190 = 44 +
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
    rw [show 50 = 6 +
      44 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_189_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_189_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_190_prefix_zero :
    (∑ x ∈ Finset.range 45,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (190 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (190 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_190_suffix_zero :
    (∑ x ∈ Finset.range 45,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (190 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_190 :
    recurrence5LeadingSquare.coeff 190 =
      -((((46771800549827266353163172634838 * 10 ^ 70 +
        6104624482616314469036113274895200074706453023796327427868124826897633) * 10 ^ 70 +
        3488923469880891157767347781162631885318397170990192378981357505332718) * 10 ^ 70 +
        7359789764964832455756070690319859400950409525094939156856129544573870) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 191 = 45 +
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
    rw [show 50 = 5 +
      45 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_190_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_190_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_191_prefix_zero :
    (∑ x ∈ Finset.range 46,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (191 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (191 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_191_suffix_zero :
    (∑ x ∈ Finset.range 46,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (191 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_191 :
    recurrence5LeadingSquare.coeff 191 =
      -((((1518218411610012736610964251804 * 10 ^ 70 +
        0857504151331239220892587356727778367571078301325235292559993977074076) * 10 ^ 70 +
        0359079653815481249227096722606317825598717545587680742894271702393416) * 10 ^ 70 +
        3288412638379560804517140607826908888391729682482307967786864872238108) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 192 = 46 +
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
    rw [show 50 = 4 +
      46 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_191_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_191_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_192_prefix_zero :
    (∑ x ∈ Finset.range 47,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (192 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (192 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_192_suffix_zero :
    (∑ x ∈ Finset.range 47,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (192 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_192 :
    recurrence5LeadingSquare.coeff 192 =
      ((((20035942949914707870622949514886 * 10 ^ 70 +
        3877994478758845193140012307932656552891918201448906815983108469298927) * 10 ^ 70 +
        0959433132760148511742548018277602923921712522118024785316340466061122) * 10 ^ 70 +
        9699542523152283146570332271478011651578344762781051170514929132963764) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 193 = 47 +
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
    rw [show 50 = 3 +
      47 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_192_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_192_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_193_prefix_zero :
    (∑ x ∈ Finset.range 48,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (193 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (193 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_193_suffix_zero :
    (∑ x ∈ Finset.range 48,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (193 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_193 :
    recurrence5LeadingSquare.coeff 193 =
      -((((20752150461589044147011438194726 * 10 ^ 70 +
        5063267210990641615171920691174185309507178270474945919646780346572539) * 10 ^ 70 +
        6679906074862077320785090323671120773976389247902542538296410656252711) * 10 ^ 70 +
        1955008446805265794987318195084715257960021494328831202050434142961136) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 194 = 48 +
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
    rw [show 50 = 2 +
      48 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_193_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_193_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_194_prefix_zero :
    (∑ x ∈ Finset.range 49,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (194 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (194 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_194_suffix_zero :
    (∑ x ∈ Finset.range 49,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (194 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_194 :
    recurrence5LeadingSquare.coeff 194 =
      ((((15178500374983483554262274701318 * 10 ^ 70 +
        2377649184698535953781744587670487054796783430173857114232521117284435) * 10 ^ 70 +
        6126231204830301007614497604769037573487123396435462579408520367534162) * 10 ^ 70 +
        3747051611586087410613057885454835753705021518531850712263544696225443) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 195 = 49 +
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
    rw [show 50 = 1 +
      49 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_194_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_194_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_195_prefix_zero :
    (∑ x ∈ Finset.range 50,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (195 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (195 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_195_suffix_zero :
    (∑ x ∈ Finset.range 50,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (195 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_195 :
    recurrence5LeadingSquare.coeff 195 =
      -((((9294831266591315350088940417749 * 10 ^ 70 +
        9324338414913948022002938164038591678483804415713493261225588872559347) * 10 ^ 70 +
        1785994110798206160407883414621684880117047693568509593943403052142198) * 10 ^ 70 +
        4536015865724733425051570819895713480118980345908855197693111453412712) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 196 = 50 +
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
  rw [recurrence5LeadingSquare_coeff_195_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_195_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_196_prefix_zero :
    (∑ x ∈ Finset.range 51,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (196 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (196 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_196_suffix_zero :
    (∑ x ∈ Finset.range 51,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (196 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_196 :
    recurrence5LeadingSquare.coeff 196 =
      ((((5049483288546871965505697155193 * 10 ^ 70 +
        1150225498553959005987996271086689148886835884811032491115940987659354) * 10 ^ 70 +
        6775617667870017512103550669956429329720952166741176191276844103351342) * 10 ^ 70 +
        1419276262716597254735310735191508025801043031581220963232439096454002) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 197 = 51 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 31 +
      51 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_196_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_196_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_197_prefix_zero :
    (∑ x ∈ Finset.range 52,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (197 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (197 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_197_suffix_zero :
    (∑ x ∈ Finset.range 52,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (197 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_197 :
    recurrence5LeadingSquare.coeff 197 =
      -((((2501220017928891549454046015972 * 10 ^ 70 +
        4913134468005643561371673837800955004991029862612884239608433772037017) * 10 ^ 70 +
        9776018170652392568844714906868043902620643033012940781369597490254093) * 10 ^ 70 +
        7020219206023952361296304267029318552411376595660629602894365608646498) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 198 = 52 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 30 +
      52 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_197_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_197_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_198_prefix_zero :
    (∑ x ∈ Finset.range 53,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (198 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (198 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_198_suffix_zero :
    (∑ x ∈ Finset.range 53,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (198 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_198 :
    recurrence5LeadingSquare.coeff 198 =
      ((((1147061609157469137530491668612 * 10 ^ 70 +
        7226631887511495590496071116242538069923343896489885738338452218407341) * 10 ^ 70 +
        8273506685043791761229861437283523399227026192062484582972197058604853) * 10 ^ 70 +
        8010727591921792896496335814707563398390887809871420687642997914505660) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 199 = 53 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 29 +
      53 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_198_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_198_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_199_prefix_zero :
    (∑ x ∈ Finset.range 54,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (199 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (199 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_199_suffix_zero :
    (∑ x ∈ Finset.range 54,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (199 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_199 :
    recurrence5LeadingSquare.coeff 199 =
      -((((491577514076117302202282675818 * 10 ^ 70 +
        1730304685388622120675000460021599174088459451948823465142022111134330) * 10 ^ 70 +
        2610614973501436611332082502829307813759858235765802646613593279360146) * 10 ^ 70 +
        0420956756164451914676801165427914068581350353609648097458755078136170) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 200 = 54 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 28 +
      54 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_199_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_199_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_200_prefix_zero :
    (∑ x ∈ Finset.range 55,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (200 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (200 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_200_suffix_zero :
    (∑ x ∈ Finset.range 55,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (200 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_200 :
    recurrence5LeadingSquare.coeff 200 =
      ((((198061891235925932342495473408 * 10 ^ 70 +
        9498084747865778350428522699530840314496334967654736545677959389938271) * 10 ^ 70 +
        4060533160980235953319451124462569648552625524265600338456728420002951) * 10 ^ 70 +
        4369514320755732654172966548694207973111417342657529628469807955600372) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 201 = 55 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 27 +
      55 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_200_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_200_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_201_prefix_zero :
    (∑ x ∈ Finset.range 56,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (201 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (201 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_201_suffix_zero :
    (∑ x ∈ Finset.range 56,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (201 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_201 :
    recurrence5LeadingSquare.coeff 201 =
      -((((75374806401241770691336945920 * 10 ^ 70 +
        8136194246935749697845272971780203811634572789704324093509860238368579) * 10 ^ 70 +
        5270950114756954897152770141244983112998371095563951482102167547796540) * 10 ^ 70 +
        0291229543040602358006500223778478877876031474532683249708895806370654) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 202 = 56 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 26 +
      56 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_201_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_201_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_202_prefix_zero :
    (∑ x ∈ Finset.range 57,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (202 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (202 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_202_suffix_zero :
    (∑ x ∈ Finset.range 57,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (202 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_202 :
    recurrence5LeadingSquare.coeff 202 =
      ((((27246209422624684572014583259 * 10 ^ 70 +
        8704846309328100879089028718175822185892250636333908276775542477334071) * 10 ^ 70 +
        9581223980950219137882133706792782665083922800020252469699766910955064) * 10 ^ 70 +
        4396671401494548121682371385494100122914578361098441664510140702762708) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 203 = 57 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 25 +
      57 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_202_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_202_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_203_prefix_zero :
    (∑ x ∈ Finset.range 58,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (203 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (203 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_203_suffix_zero :
    (∑ x ∈ Finset.range 58,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (203 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_203 :
    recurrence5LeadingSquare.coeff 203 =
      -((((9463565549019506074240843163 * 10 ^ 70 +
        9487186530062638495392676241163114506114503301770975937143156023087785) * 10 ^ 70 +
        7869170012351730535573810900159756680126190671677527918336734284063029) * 10 ^ 70 +
        8559220364539495311079620500158108742145378527706177144738079951370516) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 204 = 58 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 24 +
      58 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_203_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_203_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_204_prefix_zero :
    (∑ x ∈ Finset.range 59,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (204 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (204 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_204_suffix_zero :
    (∑ x ∈ Finset.range 59,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (204 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_204 :
    recurrence5LeadingSquare.coeff 204 =
      ((((3246923460286435711243066142 * 10 ^ 70 +
        1366542451719113800137672014268648134717964761316328906024822519609445) * 10 ^ 70 +
        2805183105578747958801565378929487184439316876416024692242755532811224) * 10 ^ 70 +
        6182849751980187546093161211854967819215143474890930079530937464666635) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 205 = 59 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 23 +
      59 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_204_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_204_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_205_prefix_zero :
    (∑ x ∈ Finset.range 60,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (205 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (205 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_205_suffix_zero :
    (∑ x ∈ Finset.range 60,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (205 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_205 :
    recurrence5LeadingSquare.coeff 205 =
      -((((1165478500197750514662113449 * 10 ^ 70 +
        7428279907055748164111838427938518641002043566895287684627043240902796) * 10 ^ 70 +
        7512873118209372292773330230139062373167550185164154315658899977514040) * 10 ^ 70 +
        9665809487191578643807817299874448498108157737705508462172607240992140) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 206 = 60 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 22 +
      60 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_205_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_205_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_206_prefix_zero :
    (∑ x ∈ Finset.range 61,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (206 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (206 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_206_suffix_zero :
    (∑ x ∈ Finset.range 61,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (206 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_206 :
    recurrence5LeadingSquare.coeff 206 =
      ((((474336807998118984160420137 * 10 ^ 70 +
        8521885588073118226501008905989863782682420700415625693030633588566042) * 10 ^ 70 +
        8430178405693829294343499355070145536576987925821349816252350738006633) * 10 ^ 70 +
        2315164955022320746962956844926789269664563444354179981555945219519716) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 207 = 61 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 21 +
      61 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_206_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_206_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_207_prefix_zero :
    (∑ x ∈ Finset.range 62,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (207 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (207 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_207_suffix_zero :
    (∑ x ∈ Finset.range 62,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (207 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_207 :
    recurrence5LeadingSquare.coeff 207 =
      -((((228175589138297078411983195 * 10 ^ 70 +
        0917942282916937152192971729686404430180843362819896698723672178922835) * 10 ^ 70 +
        3375922620329857764213557868197207252363554960347791065233544497818279) * 10 ^ 70 +
        7699361652400178740207099568983679985419419019250021169869370078313648) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 208 = 62 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 20 +
      62 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_207_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_207_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_208_prefix_zero :
    (∑ x ∈ Finset.range 63,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (208 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (208 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_208_suffix_zero :
    (∑ x ∈ Finset.range 63,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (208 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_208 :
    recurrence5LeadingSquare.coeff 208 =
      ((((123912923728941848226725876 * 10 ^ 70 +
        1733436447879476131548531791562642172209930178966186798969947298558057) * 10 ^ 70 +
        0837176470971634435251854907177802789574540888678467174283290607068894) * 10 ^ 70 +
        0222333623178034138197213722372158702007042785378554077942770718731528) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 209 = 63 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 19 +
      63 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_208_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_208_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_209_prefix_zero :
    (∑ x ∈ Finset.range 64,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (209 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (209 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_209_suffix_zero :
    (∑ x ∈ Finset.range 64,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (209 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_209 :
    recurrence5LeadingSquare.coeff 209 =
      -((((70100544410516239848470800 * 10 ^ 70 +
        5130404648657893790504567323768439600378473335142927028722229087174900) * 10 ^ 70 +
        2882913726861117023791105416149378694389788911306676299479547038688187) * 10 ^ 70 +
        5599082763576696874021963140059410508655793684132236863762243814417840) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 210 = 64 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 18 +
      64 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_209_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_209_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_210_prefix_zero :
    (∑ x ∈ Finset.range 65,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (210 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (210 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_210_suffix_zero :
    (∑ x ∈ Finset.range 65,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (210 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_210 :
    recurrence5LeadingSquare.coeff 210 =
      ((((39105907149812825762747511 * 10 ^ 70 +
        0360368187665813272597707905406469221799486486533310163989885352764200) * 10 ^ 70 +
        1373190167725137616049953796197824449382294340719723958740517920958900) * 10 ^ 70 +
        8115489125989224414751412210322221279582727167407877376835005849835440) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 211 = 65 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 17 +
      65 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_210_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_210_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_211_prefix_zero :
    (∑ x ∈ Finset.range 66,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (211 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (211 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_211_suffix_zero :
    (∑ x ∈ Finset.range 66,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (211 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_211 :
    recurrence5LeadingSquare.coeff 211 =
      -((((20994629118224934827213970 * 10 ^ 70 +
        0673641107191032933427485286392779506340768883163812629235757287301501) * 10 ^ 70 +
        5165079766987216177241276543262321219320015924255313110350176577166833) * 10 ^ 70 +
        0892711549142460103875287857335634482629335063021032749722272196085060) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 212 = 66 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 16 +
      66 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_211_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_211_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_212_prefix_zero :
    (∑ x ∈ Finset.range 67,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (212 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (212 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_212_suffix_zero :
    (∑ x ∈ Finset.range 67,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (212 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_212 :
    recurrence5LeadingSquare.coeff 212 =
      ((((10767008320033385746546252 * 10 ^ 70 +
        6501966401112609053166131724117738566689211411467315368448435296413820) * 10 ^ 70 +
        4515558740072963403706929589484915288010430984672230766027917880558084) * 10 ^ 70 +
        6297170034904554243399407129653858179371651149196417890738479381497483) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 213 = 67 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 15 +
      67 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_212_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_212_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_213_prefix_zero :
    (∑ x ∈ Finset.range 68,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (213 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (213 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_213_suffix_zero :
    (∑ x ∈ Finset.range 68,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (213 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_213 :
    recurrence5LeadingSquare.coeff 213 =
      -((((5273555039819055791058267 * 10 ^ 70 +
        0732850789538346652663696197686623878791534075323476983052920829428264) * 10 ^ 70 +
        0137599547612874360076864334063659991286588278856612314537331053577577) * 10 ^ 70 +
        8666505306986162141372673341775816118215310013927234320083335906162544) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 214 = 68 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 14 +
      68 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_213_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_213_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_214_prefix_zero :
    (∑ x ∈ Finset.range 69,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (214 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (214 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_214_suffix_zero :
    (∑ x ∈ Finset.range 69,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (214 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_214 :
    recurrence5LeadingSquare.coeff 214 =
      ((((2472659973898489151797243 * 10 ^ 70 +
        1099637456122381620108709620491250925647797335641806979304861270190094) * 10 ^ 70 +
        9188807008793619418666231061594128353507129831488293219737143810961488) * 10 ^ 70 +
        4025630494587969935303831513815379728661395299735649010960651706527615) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 215 = 69 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 13 +
      69 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_214_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_214_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_215_prefix_zero :
    (∑ x ∈ Finset.range 70,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (215 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (215 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_215_suffix_zero :
    (∑ x ∈ Finset.range 70,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (215 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_215 :
    recurrence5LeadingSquare.coeff 215 =
      -((((1113285844235815162880225 * 10 ^ 70 +
        7701074253687219398787347020629062687382176276942535024055510091530704) * 10 ^ 70 +
        6628284258263235937642365790573510646858989025807932307684281326709298) * 10 ^ 70 +
        0073727431314654348585258082613612890013175692434384037942064125531966) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 216 = 70 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 12 +
      70 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_215_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_215_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_216_prefix_zero :
    (∑ x ∈ Finset.range 71,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (216 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (216 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_216_suffix_zero :
    (∑ x ∈ Finset.range 71,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (216 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_216 :
    recurrence5LeadingSquare.coeff 216 =
      ((((482749234360082379960423 * 10 ^ 70 +
        2819320076373015599661394038816459034988387319472092697501036609444159) * 10 ^ 70 +
        2779016428878154623917981749351453710393099727035669463347530881810990) * 10 ^ 70 +
        4345700088605309616109067712494757771498328951139028606562785637946689) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 217 = 71 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 11 +
      71 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_216_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_216_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_217_prefix_zero :
    (∑ x ∈ Finset.range 72,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (217 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (217 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_217_suffix_zero :
    (∑ x ∈ Finset.range 72,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (217 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_217 :
    recurrence5LeadingSquare.coeff 217 =
      -((((202128893669259090276436 * 10 ^ 70 +
        2504291822283139603997043669949998444186432705585959735714699552506212) * 10 ^ 70 +
        8268987706097628426876675143272167467478087565081278385727016719752594) * 10 ^ 70 +
        8086221394872808065754583152285053814818585607405037152708002809829220) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 218 = 72 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 10 +
      72 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_217_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_217_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
