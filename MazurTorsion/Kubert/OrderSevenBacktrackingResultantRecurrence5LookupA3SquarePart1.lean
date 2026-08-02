/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupA3
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 5 lookup certificate: A3Square coefficient convolution

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence5A3_coeff_0
  recurrence5A3_coeff_1
  recurrence5A3_coeff_2
  recurrence5A3_coeff_3
  recurrence5A3_coeff_4
  recurrence5A3_coeff_5
  recurrence5A3_coeff_6
  recurrence5A3_coeff_7
  recurrence5A3_coeff_8
  recurrence5A3_coeff_9
  recurrence5A3_coeff_10
  recurrence5A3_coeff_11
  recurrence5A3_coeff_12
  recurrence5A3_coeff_13
  recurrence5A3_coeff_14
  recurrence5A3_coeff_15
  recurrence5A3_coeff_16
  recurrence5A3_coeff_17
  recurrence5A3_coeff_18
  recurrence5A3_coeff_19
  recurrence5A3_coeff_20
  recurrence5A3_coeff_21
  recurrence5A3_coeff_22
  recurrence5A3_coeff_23
  recurrence5A3_coeff_24
  recurrence5A3_coeff_25
  recurrence5A3_coeff_26
  recurrence5A3_coeff_27
  recurrence5A3_coeff_28
  recurrence5A3_coeff_29
  recurrence5A3_coeff_30
  recurrence5A3_coeff_31
  recurrence5A3_coeff_32
  recurrence5A3_coeff_33
  recurrence5A3_coeff_34
  recurrence5A3_coeff_35
  recurrence5A3_coeff_36
  recurrence5A3_coeff_37
  recurrence5A3_coeff_38
  recurrence5A3_coeff_39
  recurrence5A3_coeff_40
  recurrence5A3_coeff_41
  recurrence5A3_coeff_42
  recurrence5A3_coeff_43
  recurrence5A3_coeff_44
  recurrence5A3_coeff_45
  recurrence5A3_coeff_46
  recurrence5A3_coeff_47
  recurrence5A3_coeff_48
  recurrence5A3_coeff_49
  recurrence5A3_coeff_50
  recurrence5A3_coeff_51
  recurrence5A3_coeff_52
  recurrence5A3_coeff_53
  recurrence5A3_coeff_54
  recurrence5A3_coeff_55
  recurrence5A3_coeff_56
  recurrence5A3_coeff_57
  recurrence5A3_coeff_58
  recurrence5A3_coeff_59
  recurrence5A3_coeff_60
  recurrence5A3_coeff_61
  recurrence5A3_coeff_62
  recurrence5A3_coeff_63

attribute [local simp]
  recurrence5A3_coeff_64
  recurrence5A3_coeff_65
  recurrence5A3_coeff_66
  recurrence5A3_coeff_67
  recurrence5A3_coeff_68
  recurrence5A3_coeff_69
  recurrence5A3_coeff_70
  recurrence5A3_coeff_71
  recurrence5A3_coeff_72
  recurrence5A3_coeff_73
  recurrence5A3_coeff_74
  recurrence5A3_coeff_75
  recurrence5A3_coeff_76
  recurrence5A3_coeff_77
  recurrence5A3_coeff_78
  recurrence5A3_coeff_79
  recurrence5A3_coeff_80
  recurrence5A3_coeff_81
  recurrence5A3_coeff_82
  recurrence5A3_coeff_83
  recurrence5A3_coeff_84
  recurrence5A3_coeff_85
  recurrence5A3_coeff_86
  recurrence5A3_coeff_87
  recurrence5A3_coeff_88
  recurrence5A3_coeff_89
  recurrence5A3_coeff_90
  recurrence5A3_coeff_91
  recurrence5A3_coeff_92
  recurrence5A3_coeff_93
  recurrence5A3_coeff_94
  recurrence5A3_coeff_95
  recurrence5A3_coeff_96
  recurrence5A3_coeff_97
  recurrence5A3_coeff_98
  recurrence5A3_coeff_99
  recurrence5A3_coeff_100
  recurrence5A3_coeff_101
  recurrence5A3_coeff_102
  recurrence5A3_coeff_103
  recurrence5A3_coeff_104
  recurrence5A3_coeff_105
  recurrence5A3_coeff_106
  recurrence5A3_coeff_107
  recurrence5A3_coeff_108
  recurrence5A3_coeff_109
  recurrence5A3_coeff_110
  recurrence5A3_coeff_111
  recurrence5A3_coeff_112
  recurrence5A3_coeff_113
  recurrence5A3_coeff_114
  recurrence5A3_coeff_115
  recurrence5A3_coeff_116
  recurrence5A3_coeff_117
  recurrence5A3_coeff_118
  recurrence5A3_coeff_119
  recurrence5A3_coeff_120
  recurrence5A3_coeff_121
  recurrence5A3_coeff_122
  recurrence5A3_coeff_123
  recurrence5A3_coeff_124
  recurrence5A3_coeff_125
  recurrence5A3_coeff_126
  recurrence5A3_coeff_127

attribute [local simp]
  recurrence5A3_coeff_128
  recurrence5A3_coeff_129
  recurrence5A3_coeff_130
  recurrence5A3_coeff_131
  recurrence5A3_coeff_132
  recurrence5A3_coeff_133
  recurrence5A3_coeff_134
  recurrence5A3_coeff_135
  recurrence5A3_coeff_136
  recurrence5A3_coeff_137
  recurrence5A3_coeff_138
  recurrence5A3_coeff_139
  recurrence5A3_coeff_140
  recurrence5A3_coeff_141
  recurrence5A3_coeff_142
  recurrence5A3_coeff_143
  recurrence5A3_coeff_144
  recurrence5A3_coeff_145
  recurrence5A3_coeff_146
  recurrence5A3_coeff_147
  recurrence5A3_coeff_148
  recurrence5A3_coeff_149
  recurrence5A3_coeff_150
  recurrence5A3_coeff_151
  recurrence5A3_coeff_152
  recurrence5A3_coeff_153
  recurrence5A3_coeff_154
  recurrence5A3_coeff_155
  recurrence5A3_coeff_156
  recurrence5A3_coeff_157
  recurrence5A3_coeff_158
  recurrence5A3_coeff_159
  recurrence5A3_coeff_160
  recurrence5A3_coeff_161
  recurrence5A3_coeff_162
  recurrence5A3_coeff_163
  recurrence5A3_coeff_164

private theorem recurrence5A3Square_coeff_227_prefix_zero :
    (∑ x ∈ Finset.range 63,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (227 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (227 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_227_suffix_zero :
    (∑ x ∈ Finset.range 63,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (227 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_227 :
    recurrence5A3Square.coeff 227 =
      -(((9863786106060946659895243164038940582835547008739481 * 10 ^ 70 +
        6268962158020213180539098267664061281320550355558310670720150515228631) * 10 ^ 70 +
        4660546637758217690907648061103474862876356803521759168123542488275154) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 228 = 63 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 6 +
      63 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_227_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_227_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_228_prefix_zero :
    (∑ x ∈ Finset.range 64,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (228 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (228 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_228_suffix_zero :
    (∑ x ∈ Finset.range 64,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (228 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_228 :
    recurrence5A3Square.coeff 228 =
      (((3327390662253230065263585741053257804594838508238441 * 10 ^ 70 +
        0034262328033077576094649164565491525339297236444574295995392376857624) * 10 ^ 70 +
        9016985906538316220016824270310622904242563127019359931075899334609742) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 229 = 64 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 5 +
      64 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_228_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_228_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_229_prefix_zero :
    (∑ x ∈ Finset.range 65,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (229 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (229 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_229_suffix_zero :
    (∑ x ∈ Finset.range 65,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (229 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_229 :
    recurrence5A3Square.coeff 229 =
      -(((1042080273441837026274620434825161832200176618316262 * 10 ^ 70 +
        7534378460067765729379544213631771075849571508175698367657603068213755) * 10 ^ 70 +
        9742534600781918019541202881550787397344244715678160996826995080833454) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 230 = 65 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 4 +
      65 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_229_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_229_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_230_prefix_zero :
    (∑ x ∈ Finset.range 66,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (230 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (230 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_230_suffix_zero :
    (∑ x ∈ Finset.range 66,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (230 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_230 :
    recurrence5A3Square.coeff 230 =
      (((294141735903972541675598794454111604051753641289028 * 10 ^ 70 +
        7346232118413586022497792591820616375561285177939680961970376745638991) * 10 ^ 70 +
        3696038297573702563916907870919654801775277554595251981083731398111005) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 231 = 66 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 3 +
      66 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_230_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_230_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_231_prefix_zero :
    (∑ x ∈ Finset.range 67,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (231 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (231 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_231_suffix_zero :
    (∑ x ∈ Finset.range 67,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (231 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_231 :
    recurrence5A3Square.coeff 231 =
      -(((69757301151839119149616984101688122321836041758324 * 10 ^ 70 +
        4332869409351501319543651916850252145753528290610465769088702035746084) * 10 ^ 70 +
        0201442661457077328203292803245536315760737854862653905520864459214850) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 232 = 67 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 2 +
      67 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_231_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_231_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_232_prefix_zero :
    (∑ x ∈ Finset.range 68,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (232 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (232 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_232_suffix_zero :
    (∑ x ∈ Finset.range 68,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (232 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_232 :
    recurrence5A3Square.coeff 232 =
      (((10698422328704931630203383659249240987334220674228 * 10 ^ 70 +
        1373757185287399210843455314523946972404339149365724733598118903654697) * 10 ^ 70 +
        6411824475133086503759627463383734474210153929987718537522420516703881) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 233 = 68 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 1 +
      68 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_232_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_232_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_233_prefix_zero :
    (∑ x ∈ Finset.range 69,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (233 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (233 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_233_suffix_zero :
    (∑ x ∈ Finset.range 69,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (233 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_233 :
    recurrence5A3Square.coeff 233 =
      (((1356979953850069694260420975309982046995547994428 * 10 ^ 70 +
        9377658407004220761627916830792815205434853015803241034857808260888672) * 10 ^ 70 +
        3805743759958373153469129447085670773656527631958735379191888274528044) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 234 = 69 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_233_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_233_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_234_prefix_zero :
    (∑ x ∈ Finset.range 70,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (234 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (234 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_234_suffix_zero :
    (∑ x ∈ Finset.range 70,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (234 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_234 :
    recurrence5A3Square.coeff 234 =
      -(((2187898632086072669765957228404204122600800525894 * 10 ^ 70 +
        8273195283863500947014341580921937259053540796906149344259232886493019) * 10 ^ 70 +
        5295866940852682412749839596665464288332940593064468438027492362991758) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 235 = 70 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 31 +
      70 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_234_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_234_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_235_prefix_zero :
    (∑ x ∈ Finset.range 71,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (235 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (235 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_235_suffix_zero :
    (∑ x ∈ Finset.range 71,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (235 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_235 :
    recurrence5A3Square.coeff 235 =
      (((1277816701540295082897364844916533770982724376376 * 10 ^ 70 +
        5536827200072258773751221782701161940634733913862976040301710424489730) * 10 ^ 70 +
        8142230156759574306179911089994000499076544364263951490789741007775896) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 236 = 71 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 30 +
      71 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_235_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_235_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_236_prefix_zero :
    (∑ x ∈ Finset.range 72,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (236 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (236 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_236_suffix_zero :
    (∑ x ∈ Finset.range 72,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (236 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_236 :
    recurrence5A3Square.coeff 236 =
      -(((577510491766728576647334737969185702025823382398 * 10 ^ 70 +
        9737845706284430134284707483358877161037015399578535806495267709370024) * 10 ^ 70 +
        4489163116976033864509274350570459948278984340358298226142119690700602) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 237 = 72 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 29 +
      72 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_236_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_236_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_237_prefix_zero :
    (∑ x ∈ Finset.range 73,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (237 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (237 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_237_suffix_zero :
    (∑ x ∈ Finset.range 73,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (237 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_237 :
    recurrence5A3Square.coeff 237 =
      (((226335984191438391201701292385604159407366477915 * 10 ^ 70 +
        8171223627044796790598385197882056530655783540740513040180653913736191) * 10 ^ 70 +
        9913357034217465001681479128972203185904311209083391722417391803572366) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 238 = 73 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 28 +
      73 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_237_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_237_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_238_prefix_zero :
    (∑ x ∈ Finset.range 74,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (238 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (238 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_238_suffix_zero :
    (∑ x ∈ Finset.range 74,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (238 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_238 :
    recurrence5A3Square.coeff 238 =
      -(((79648411145801183209372473226741802496692629164 * 10 ^ 70 +
        5175424143104495514808915443212401617679447022970479913754385401606201) * 10 ^ 70 +
        3478615753608091916893215821174545184697309890708848039746486837985956) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 239 = 74 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 27 +
      74 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_238_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_238_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_239_prefix_zero :
    (∑ x ∈ Finset.range 75,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (239 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (239 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_239_suffix_zero :
    (∑ x ∈ Finset.range 75,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (239 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_239 :
    recurrence5A3Square.coeff 239 =
      (((25340169337212719312257500430828255890530738381 * 10 ^ 70 +
        1384466588995233411081456477540927575349131185347917409720284013035625) * 10 ^ 70 +
        2700762255881772524070097615191039079509682982866300128940098224319758) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 240 = 75 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 26 +
      75 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_239_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_239_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_240_prefix_zero :
    (∑ x ∈ Finset.range 76,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (240 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (240 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_240_suffix_zero :
    (∑ x ∈ Finset.range 76,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (240 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_240 :
    recurrence5A3Square.coeff 240 =
      -(((7173465154104085860331003750167322418113094192 * 10 ^ 70 +
        3134916351181252165802645152999419722442259801051704237771838049736923) * 10 ^ 70 +
        1269809166469419063623986418544404180777525979322647184412335409161806) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 241 = 76 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 25 +
      76 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_240_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_240_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_241_prefix_zero :
    (∑ x ∈ Finset.range 77,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (241 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (241 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_241_suffix_zero :
    (∑ x ∈ Finset.range 77,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (241 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_241 :
    recurrence5A3Square.coeff 241 =
      (((1698876651408819349440568767394749332995193260 * 10 ^ 70 +
        3017688737393751981508609409980090511444743392990176648592547716755437) * 10 ^ 70 +
        8136659518758265552187763018577203090208661116673163949509411407521774) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 242 = 77 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 24 +
      77 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_241_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_241_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_242_prefix_zero :
    (∑ x ∈ Finset.range 78,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (242 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (242 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_242_suffix_zero :
    (∑ x ∈ Finset.range 78,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (242 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_242 :
    recurrence5A3Square.coeff 242 =
      -(((258028669874922555141849154914948531531143068 * 10 ^ 70 +
        4185002420862762208270501550420846948854391443655219083016159429884023) * 10 ^ 70 +
        8291426642499723222070565953119665989206108824628475345746537603177036) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 243 = 78 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 23 +
      78 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_242_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_242_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_243_prefix_zero :
    (∑ x ∈ Finset.range 79,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (243 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (243 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_243_suffix_zero :
    (∑ x ∈ Finset.range 79,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (243 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_243 :
    recurrence5A3Square.coeff 243 =
      -(((38135404313704202673643798871465364499112633 * 10 ^ 70 +
        3595482093135690549096720891169163075886847219251028977950712098162354) * 10 ^ 70 +
        0828411257292884179088003057531966676919118051127322508216469366229928) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 244 = 79 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 22 +
      79 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_243_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_243_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_244_prefix_zero :
    (∑ x ∈ Finset.range 80,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (244 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (244 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_244_suffix_zero :
    (∑ x ∈ Finset.range 80,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (244 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_244 :
    recurrence5A3Square.coeff 244 =
      (((59734163286858137181817486877296014763373384 * 10 ^ 70 +
        1760074355016729546754166240576593299999875147884788495396009949473132) * 10 ^ 70 +
        4736739783631726080470501376985246673371637875967456242665297441315642) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 245 = 80 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 21 +
      80 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_244_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_244_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_245_prefix_zero :
    (∑ x ∈ Finset.range 81,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (245 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (245 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_245_suffix_zero :
    (∑ x ∈ Finset.range 81,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (245 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_245 :
    recurrence5A3Square.coeff 245 =
      -(((36950416214128490212349369616234088842314699 * 10 ^ 70 +
        7937770025912132248673896929661582681831539065424445432842951779492486) * 10 ^ 70 +
        1264391037193204330437217860367342617044860801250676466763306675423176) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 246 = 81 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 20 +
      81 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_245_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_245_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_246_prefix_zero :
    (∑ x ∈ Finset.range 82,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (246 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (246 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_246_suffix_zero :
    (∑ x ∈ Finset.range 82,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (246 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_246 :
    recurrence5A3Square.coeff 246 =
      (((18248522266597075142797297626612555868278423 * 10 ^ 70 +
        5355866542985201301979270670978220616999755525236248257301986789879521) * 10 ^ 70 +
        6984533006018987394775679445467939829791018643935999879823161056193044) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 247 = 82 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 19 +
      82 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_246_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_246_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_247_prefix_zero :
    (∑ x ∈ Finset.range 83,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (247 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (247 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_247_suffix_zero :
    (∑ x ∈ Finset.range 83,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (247 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_247 :
    recurrence5A3Square.coeff 247 =
      -(((8055925369670958836565011096383408302769762 * 10 ^ 70 +
        2197859761516452868020194188484721838975774366184712266581142456388709) * 10 ^ 70 +
        8964639350534164149820331257568324997294799557849004600290900043185134) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 248 = 83 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 18 +
      83 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_247_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_247_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_248_prefix_zero :
    (∑ x ∈ Finset.range 84,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (248 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (248 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_248_suffix_zero :
    (∑ x ∈ Finset.range 84,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (248 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_248 :
    recurrence5A3Square.coeff 248 =
      (((3303358796667169242072138135497849002249370 * 10 ^ 70 +
        8542946355904278356391972704929879756478874033661941931600568713269966) * 10 ^ 70 +
        9902215613607257913742423408451127996352377203699121715219939025867094) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 249 = 84 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 17 +
      84 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_248_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_248_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_249_prefix_zero :
    (∑ x ∈ Finset.range 85,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (249 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (249 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_249_suffix_zero :
    (∑ x ∈ Finset.range 85,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (249 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_249 :
    recurrence5A3Square.coeff 249 =
      -(((1278484688740372886546168658312401438064294 * 10 ^ 70 +
        9144948454214835618964753958380741902132379083308684218492318165970949) * 10 ^ 70 +
        1903589423481883932809440808930995838813875966492399353228625727793712) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 250 = 85 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 16 +
      85 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_249_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_249_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_250_prefix_zero :
    (∑ x ∈ Finset.range 86,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (250 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (250 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_250_suffix_zero :
    (∑ x ∈ Finset.range 86,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (250 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_250 :
    recurrence5A3Square.coeff 250 =
      (((470138887996661974735376645374857914551367 * 10 ^ 70 +
        6057712251240985076990272319199005019744482851105622985801828335792455) * 10 ^ 70 +
        5343593201009107219869170205681939150584155516427621843475428436576789) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 251 = 86 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 15 +
      86 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_250_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_250_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_251_prefix_zero :
    (∑ x ∈ Finset.range 87,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (251 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (251 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_251_suffix_zero :
    (∑ x ∈ Finset.range 87,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (251 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_251 :
    recurrence5A3Square.coeff 251 =
      -(((164544163191224738147058766609017939163831 * 10 ^ 70 +
        9780593611452194163646029210642185814675821336937300339601711899781935) * 10 ^ 70 +
        2501575891864956754917897045872894347620059423788879461092334134957618) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 252 = 87 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 14 +
      87 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_251_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_251_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_252_prefix_zero :
    (∑ x ∈ Finset.range 88,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (252 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (252 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_252_suffix_zero :
    (∑ x ∈ Finset.range 88,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (252 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_252 :
    recurrence5A3Square.coeff 252 =
      (((54704517564068850334116312370239481653997 * 10 ^ 70 +
        7317138072052655232059693396377100800116380849676586988246048393310951) * 10 ^ 70 +
        8582372297185505932721437206853128631802049403470144723737853115146962) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 253 = 88 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 13 +
      88 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_252_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_252_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_253_prefix_zero :
    (∑ x ∈ Finset.range 89,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (253 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (253 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_253_suffix_zero :
    (∑ x ∈ Finset.range 89,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (253 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_253 :
    recurrence5A3Square.coeff 253 =
      -(((17174242424763704066846818173457531031785 * 10 ^ 70 +
        1805455673394700875682585630646390359499226067578541719550201145458015) * 10 ^ 70 +
        9673618630167568701175693534502847015347853567398400569388319552177882) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 254 = 89 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 12 +
      89 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_253_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_253_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_254_prefix_zero :
    (∑ x ∈ Finset.range 90,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (254 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (254 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_254_suffix_zero :
    (∑ x ∈ Finset.range 90,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (254 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_254 :
    recurrence5A3Square.coeff 254 =
      (((5030344123167268553006210486394499626029 * 10 ^ 70 +
        1965192448883004677936527687895510834754258827088651253200751021044405) * 10 ^ 70 +
        0535010667741323358696784724913071338402535353692927514191132633458168) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 255 = 90 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 11 +
      90 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_254_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_254_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_255_prefix_zero :
    (∑ x ∈ Finset.range 91,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (255 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (255 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_255_suffix_zero :
    (∑ x ∈ Finset.range 91,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (255 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_255 :
    recurrence5A3Square.coeff 255 =
      -(((1341605559374980456473750047628504408089 * 10 ^ 70 +
        6654621921636803413906733082327756053769564253579520223537590109146588) * 10 ^ 70 +
        1260931267207237585430900218591489225792350640693572475820619443579456) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 256 = 91 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 10 +
      91 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_255_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_255_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_256_prefix_zero :
    (∑ x ∈ Finset.range 92,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (256 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (256 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_256_suffix_zero :
    (∑ x ∈ Finset.range 92,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (256 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_256 :
    recurrence5A3Square.coeff 256 =
      (((308142034316075907110093010684945385238 * 10 ^ 70 +
        1152036472428270852420567875473275427292273764597343362517201412169998) * 10 ^ 70 +
        6589517508955064504984670998901097305963004884587480272591587069098425) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 257 = 92 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 9 +
      92 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_256_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_256_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_257_prefix_zero :
    (∑ x ∈ Finset.range 93,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (257 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (257 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_257_suffix_zero :
    (∑ x ∈ Finset.range 93,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (257 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_257 :
    recurrence5A3Square.coeff 257 =
      -(((50911662331316659281509188252154254661 * 10 ^ 70 +
        9671203364048383514738810638220613144716787905961663921770358855669260) * 10 ^ 70 +
        2423466363005084817294606517645323484708243924985953793441001200095692) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 258 = 93 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 8 +
      93 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_257_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_257_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_258_prefix_zero :
    (∑ x ∈ Finset.range 94,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (258 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (258 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_258_suffix_zero :
    (∑ x ∈ Finset.range 94,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (258 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_258 :
    recurrence5A3Square.coeff 258 =
      -(((574186009104048688978227298701855868 * 10 ^ 70 +
        6464632530820291052208130890460484552878936252806683913962563975890103) * 10 ^ 70 +
        6516093241494538100535483005055785963010393628565651921026346454862899) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 259 = 94 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 7 +
      94 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_258_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_258_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_259_prefix_zero :
    (∑ x ∈ Finset.range 95,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (259 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (259 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_259_suffix_zero :
    (∑ x ∈ Finset.range 95,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (259 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_259 :
    recurrence5A3Square.coeff 259 =
      (((5578668773984236591091009196510017645 * 10 ^ 70 +
        8999249563864875742830357087007609452850480638803261688526505094402288) * 10 ^ 70 +
        7702568928516920617608291215583564483568382458492442507898480978357092) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 260 = 95 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 6 +
      95 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_259_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_259_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_260_prefix_zero :
    (∑ x ∈ Finset.range 96,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (260 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (260 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_260_suffix_zero :
    (∑ x ∈ Finset.range 96,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (260 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_260 :
    recurrence5A3Square.coeff 260 =
      -(((3334112660647948060575286417910211398 * 10 ^ 70 +
        7651907855022458592531008900445434367523684297426857641417032228124720) * 10 ^ 70 +
        5948763890431048923864495227524428533600508031678286034497707629567942) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 261 = 96 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 5 +
      96 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_260_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_260_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_261_prefix_zero :
    (∑ x ∈ Finset.range 97,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (261 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (261 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_261_suffix_zero :
    (∑ x ∈ Finset.range 97,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (261 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_261 :
    recurrence5A3Square.coeff 261 =
      (((1455768857478374444014651615142791987 * 10 ^ 70 +
        6830811326724179512477290716215888118500591738744504196790363291984189) * 10 ^ 70 +
        5158962923358532380026370955869923661703683711100039827203700552434410) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 262 = 97 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 4 +
      97 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_261_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_261_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_262_prefix_zero :
    (∑ x ∈ Finset.range 98,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (262 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (262 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_262_suffix_zero :
    (∑ x ∈ Finset.range 98,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (262 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_262 :
    recurrence5A3Square.coeff 262 =
      -(((545044450038199306489132070840234251 * 10 ^ 70 +
        3924424866766999831658997047259623956915413462849598760375293488014315) * 10 ^ 70 +
        5344256197727913316517825041066732081144577987877587266516353125509603) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 263 = 98 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 3 +
      98 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_262_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_262_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_263_prefix_zero :
    (∑ x ∈ Finset.range 99,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (263 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (263 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_263_suffix_zero :
    (∑ x ∈ Finset.range 99,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (263 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_263 :
    recurrence5A3Square.coeff 263 =
      (((183721024687946961337704768433862225 * 10 ^ 70 +
        8521529644921271095100586702880714206389371424107778026763234004351546) * 10 ^ 70 +
        0683034661267868638055431137389473970732495100854206676515090717151762) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 264 = 99 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 2 +
      99 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_263_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_263_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_264_prefix_zero :
    (∑ x ∈ Finset.range 100,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (264 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (264 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_264_suffix_zero :
    (∑ x ∈ Finset.range 100,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (264 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_264 :
    recurrence5A3Square.coeff 264 =
      -(((56678292895620847571572813203507415 * 10 ^ 70 +
        0212615416121228937855683161144890322265702602585470854359499563289961) * 10 ^ 70 +
        8850328713233594771633016095512339774948271537466366827591929773336191) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 265 = 100 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 1 +
      100 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_264_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_264_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_265_prefix_zero :
    (∑ x ∈ Finset.range 101,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (265 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (265 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_265_suffix_zero :
    (∑ x ∈ Finset.range 101,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (265 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_265 :
    recurrence5A3Square.coeff 265 =
      (((15941262851573140534019573045660360 * 10 ^ 70 +
        0944166358771266867303326432388661403236963035216827780138522054578531) * 10 ^ 70 +
        1729579863340965506408134596030603710526744834452347525558413163829008) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 266 = 101 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_265_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_265_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_266_prefix_zero :
    (∑ x ∈ Finset.range 102,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (266 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (266 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_266_suffix_zero :
    (∑ x ∈ Finset.range 102,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (266 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_266 :
    recurrence5A3Square.coeff 266 =
      -(((3953267780498142550257384714043971 * 10 ^ 70 +
        1834059623786669298691571819313447859796415947366391712903435609202176) * 10 ^ 70 +
        8734474365554066791052758579723958042265026360162179282358710673127788) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 267 = 102 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 31 +
      102 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_266_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_266_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_267_prefix_zero :
    (∑ x ∈ Finset.range 103,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (267 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (267 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_267_suffix_zero :
    (∑ x ∈ Finset.range 103,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (267 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_267 :
    recurrence5A3Square.coeff 267 =
      (((766892369303211169671441666501498 * 10 ^ 70 +
        0367261518632822623423600771744624257479045595235285693655530353148234) * 10 ^ 70 +
        5261151465305579970057120273901355400706245110276001779398700918554636) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 268 = 103 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 30 +
      103 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_267_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_267_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_268_prefix_zero :
    (∑ x ∈ Finset.range 104,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (268 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (268 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_268_suffix_zero :
    (∑ x ∈ Finset.range 104,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (268 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_268 :
    recurrence5A3Square.coeff 268 =
      -(((48072498642739110898786226971134 * 10 ^ 70 +
        3844869347445869772000763398748001749206199136276406287102896372700778) * 10 ^ 70 +
        4069345588104466708594022116585772453270303866031774831257512275216206) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 269 = 104 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 29 +
      104 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_268_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_268_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_269_prefix_zero :
    (∑ x ∈ Finset.range 105,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (269 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (269 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_269_suffix_zero :
    (∑ x ∈ Finset.range 105,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (269 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_269 :
    recurrence5A3Square.coeff 269 =
      -(((58080386054114705175765005529005 * 10 ^ 70 +
        5710310171084920914007420747272214652558339974890808652278204354717063) * 10 ^ 70 +
        6395625081101474708619572645258651026191200912840574180357884510624062) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 270 = 105 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 28 +
      105 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_269_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_269_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_270_prefix_zero :
    (∑ x ∈ Finset.range 106,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (270 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (270 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_270_suffix_zero :
    (∑ x ∈ Finset.range 106,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (270 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_270 :
    recurrence5A3Square.coeff 270 =
      (((44521501645932358387402491497651 * 10 ^ 70 +
        1746618052231392041759640060399553650616463268818241193757677490775830) * 10 ^ 70 +
        9908076144595218649648175528314173087312265359600310589131862066668773) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 271 = 106 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 27 +
      106 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_270_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_270_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_271_prefix_zero :
    (∑ x ∈ Finset.range 107,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (271 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (271 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_271_suffix_zero :
    (∑ x ∈ Finset.range 107,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (271 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_271 :
    recurrence5A3Square.coeff 271 =
      -(((22952261970391898698392704459081 * 10 ^ 70 +
        6812156067680055994476223993403945376417390723514408448067566525352757) * 10 ^ 70 +
        7877550128686187284625895739021501400918327903946343553032020190593340) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 272 = 107 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 26 +
      107 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_271_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_271_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_272_prefix_zero :
    (∑ x ∈ Finset.range 108,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (272 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (272 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_272_suffix_zero :
    (∑ x ∈ Finset.range 108,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (272 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_272 :
    recurrence5A3Square.coeff 272 =
      (((10122461015220483253867581322286 * 10 ^ 70 +
        3808353127084238359400328243600115387765516379970859688249924474044741) * 10 ^ 70 +
        8686831950385050515760309760341609487821545969952658731862767789259513) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 273 = 108 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 25 +
      108 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_272_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_272_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_273_prefix_zero :
    (∑ x ∈ Finset.range 109,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (273 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (273 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_273_suffix_zero :
    (∑ x ∈ Finset.range 109,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (273 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_273 :
    recurrence5A3Square.coeff 273 =
      -(((4078468639387832061993873054170 * 10 ^ 70 +
        1315650817977266988024870976931737535632801287385431956248721731958537) * 10 ^ 70 +
        8195105717597863808537723357415919744218725053903421743319202191981190) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 274 = 109 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 24 +
      109 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_273_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_273_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_274_prefix_zero :
    (∑ x ∈ Finset.range 110,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (274 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (274 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_274_suffix_zero :
    (∑ x ∈ Finset.range 110,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (274 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_274 :
    recurrence5A3Square.coeff 274 =
      (((1542268978599714547719110761198 * 10 ^ 70 +
        7343392751782459136743796641247670993018411279847251985765011486984497) * 10 ^ 70 +
        6510200429684408848744089431231372521773281929270730796220522786241769) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 275 = 110 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 23 +
      110 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_274_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_274_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_275_prefix_zero :
    (∑ x ∈ Finset.range 111,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (275 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (275 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_275_suffix_zero :
    (∑ x ∈ Finset.range 111,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (275 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_275 :
    recurrence5A3Square.coeff 275 =
      -(((554280908756674928419392652157 * 10 ^ 70 +
        4081640091510426882318701139257758736083797561739204261634844276557759) * 10 ^ 70 +
        5501901233976921968827968822123054901653009791207224014513147442443858) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 276 = 111 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 22 +
      111 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_275_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_275_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_276_prefix_zero :
    (∑ x ∈ Finset.range 112,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (276 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (276 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_276_suffix_zero :
    (∑ x ∈ Finset.range 112,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (276 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_276 :
    recurrence5A3Square.coeff 276 =
      (((190380601057782506908449348647 * 10 ^ 70 +
        0342450857566265762870245846720024150353546525064515238212168173840461) * 10 ^ 70 +
        9814305985146992539367056841919876415106936717513567013255825498024470) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 277 = 112 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 21 +
      112 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_276_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_276_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_277_prefix_zero :
    (∑ x ∈ Finset.range 113,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (277 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (277 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_277_suffix_zero :
    (∑ x ∈ Finset.range 113,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (277 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_277 :
    recurrence5A3Square.coeff 277 =
      -(((62599117109886620794378052715 * 10 ^ 70 +
        1196906821022107757011110780208084346488703106896774423798381985688554) * 10 ^ 70 +
        9264222501682931558048847240924956805306726471740759029874534839981648) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 278 = 113 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 20 +
      113 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_277_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_277_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_278_prefix_zero :
    (∑ x ∈ Finset.range 114,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (278 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (278 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_278_suffix_zero :
    (∑ x ∈ Finset.range 114,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (278 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_278 :
    recurrence5A3Square.coeff 278 =
      (((19694568437178122814253513316 * 10 ^ 70 +
        8394229879795067756925778384768204842654589793671597378939521825686360) * 10 ^ 70 +
        7153961166288385468443728217913439515838527984850879843912224346682176) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 279 = 114 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 19 +
      114 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_278_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_278_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_279_prefix_zero :
    (∑ x ∈ Finset.range 115,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (279 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (279 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_279_suffix_zero :
    (∑ x ∈ Finset.range 115,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (279 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_279 :
    recurrence5A3Square.coeff 279 =
      -(((5918942964183119052958189008 * 10 ^ 70 +
        7342992400360799440162157172124518284697427307453465032252990020837111) * 10 ^ 70 +
        3783557644155988241374030826113527431944656146378681134591321153498034) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 280 = 115 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 18 +
      115 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_279_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_279_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_280_prefix_zero :
    (∑ x ∈ Finset.range 116,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (280 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (280 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_280_suffix_zero :
    (∑ x ∈ Finset.range 116,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (280 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_280 :
    recurrence5A3Square.coeff 280 =
      (((1695649302820669129330498759 * 10 ^ 70 +
        6461903114954060796125462570509336052790442307798937406581569922960427) * 10 ^ 70 +
        0192446835191285881760159521088132637219268982971366232028879233331636) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 281 = 116 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 17 +
      116 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_280_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_280_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_281_prefix_zero :
    (∑ x ∈ Finset.range 117,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (281 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (281 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_281_suffix_zero :
    (∑ x ∈ Finset.range 117,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (281 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_281 :
    recurrence5A3Square.coeff 281 =
      -(((461999393161967501771354651 * 10 ^ 70 +
        4959452704497053233963000343947176414707262148817915407555066158783376) * 10 ^ 70 +
        8424730623528663979899715676262739573980066332059808078329188615989472) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 282 = 117 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 16 +
      117 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_281_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_281_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_282_prefix_zero :
    (∑ x ∈ Finset.range 118,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (282 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (282 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_282_suffix_zero :
    (∑ x ∈ Finset.range 118,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (282 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_282 :
    recurrence5A3Square.coeff 282 =
      (((119451949604813817865202471 * 10 ^ 70 +
        5161213903776152066887100537313408202691622567615654535507313861430529) * 10 ^ 70 +
        4999207593450708661545048330327703007492182360610871011037898070205901) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 283 = 118 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 15 +
      118 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_282_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_282_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_283_prefix_zero :
    (∑ x ∈ Finset.range 119,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (283 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (283 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_283_suffix_zero :
    (∑ x ∈ Finset.range 119,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (283 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_283 :
    recurrence5A3Square.coeff 283 =
      -(((29244970562886960795673399 * 10 ^ 70 +
        2901012461385279094548165313112450960898681421393981587160772078794418) * 10 ^ 70 +
        8805705355418529919209630045111211920695801794051948107399256743676882) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 284 = 119 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 14 +
      119 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_283_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_283_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_284_prefix_zero :
    (∑ x ∈ Finset.range 120,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (284 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (284 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_284_suffix_zero :
    (∑ x ∈ Finset.range 120,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (284 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_284 :
    recurrence5A3Square.coeff 284 =
      (((6765221369495189324079888 * 10 ^ 70 +
        1160289132511444932672873449456386230345585477992657863858511836869806) * 10 ^ 70 +
        0874579998026914122868117081397781552843159016632761268236524820659060) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 285 = 120 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 13 +
      120 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_284_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_284_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_285_prefix_zero :
    (∑ x ∈ Finset.range 121,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (285 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (285 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_285_suffix_zero :
    (∑ x ∈ Finset.range 121,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (285 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_285 :
    recurrence5A3Square.coeff 285 =
      -(((1475448547878403200060148 * 10 ^ 70 +
        6814222860669077437287494930949892086173042224234184096470217698388343) * 10 ^ 70 +
        9226442704938463583174088460508036178392392694575751678240564219044646) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 286 = 121 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 12 +
      121 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_285_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_285_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_286_prefix_zero :
    (∑ x ∈ Finset.range 122,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (286 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (286 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_286_suffix_zero :
    (∑ x ∈ Finset.range 122,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (286 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_286 :
    recurrence5A3Square.coeff 286 =
      (((302654078777630204714546 * 10 ^ 70 +
        4358998162296185008913817888963156929822698146488899478862138986372066) * 10 ^ 70 +
        6933180931336054894913362245572971118593097268356780348283853479286004) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 287 = 122 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 11 +
      122 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_286_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_286_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_287_prefix_zero :
    (∑ x ∈ Finset.range 123,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (287 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (287 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_287_suffix_zero :
    (∑ x ∈ Finset.range 123,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (287 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_287 :
    recurrence5A3Square.coeff 287 =
      -(((58238450266995685155655 * 10 ^ 70 +
        3787543609657986333508687856603131952917480400435599030403815421844585) * 10 ^ 70 +
        4965075340818367395513351304100599533920021224780554537115901934037196) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 288 = 123 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 10 +
      123 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_287_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_287_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_288_prefix_zero :
    (∑ x ∈ Finset.range 124,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (288 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (288 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_288_suffix_zero :
    (∑ x ∈ Finset.range 124,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (288 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_288 :
    recurrence5A3Square.coeff 288 =
      (((10481663149626812092189 * 10 ^ 70 +
        7804350972734008760725525884244019458867937409394470081820004922124789) * 10 ^ 70 +
        1329009947913932855900008173383201528478235506124799217321004107895744) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 289 = 124 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 9 +
      124 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_288_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_288_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_289_prefix_zero :
    (∑ x ∈ Finset.range 125,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (289 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (289 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_289_suffix_zero :
    (∑ x ∈ Finset.range 125,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (289 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_289 :
    recurrence5A3Square.coeff 289 =
      -(((1758526262210859554112 * 10 ^ 70 +
        5105626005878662583436209303545463588614700747105183489631728545348543) * 10 ^ 70 +
        6290327784864622836697683809237634635167535603947754712279874636119864) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 290 = 125 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 8 +
      125 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_289_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_289_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_290_prefix_zero :
    (∑ x ∈ Finset.range 126,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (290 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (290 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_290_suffix_zero :
    (∑ x ∈ Finset.range 126,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (290 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_290 :
    recurrence5A3Square.coeff 290 =
      (((273969934025153770595 * 10 ^ 70 +
        7456811772330498773637642418937815078685873668449008759712655260869811) * 10 ^ 70 +
        1365283298216877735336627051077938337279028800451563302834096389346671) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 291 = 126 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 7 +
      126 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_290_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_290_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_291_prefix_zero :
    (∑ x ∈ Finset.range 127,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (291 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (291 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_291_suffix_zero :
    (∑ x ∈ Finset.range 127,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (291 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_291 :
    recurrence5A3Square.coeff 291 =
      -(((39463404540982304115 * 10 ^ 70 +
        2840729307440414769911907200915892049564714523975714815767165105061040) * 10 ^ 70 +
        7934784633772434205867729707790874479120638008854858824326902046166190) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 292 = 127 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 6 +
      127 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_291_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_291_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_292_prefix_zero :
    (∑ x ∈ Finset.range 128,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (292 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (292 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_292_suffix_zero :
    (∑ x ∈ Finset.range 128,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (292 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_292 :
    recurrence5A3Square.coeff 292 =
      (((5229414189201611741 * 10 ^ 70 +
        3716208942460500640744006023284100592023587951659596469786587219766177) * 10 ^ 70 +
        3909399734859177476338441963174293567022899108390776586916896860554297) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 293 = 128 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 5 +
      128 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_292_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_292_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_293_prefix_zero :
    (∑ x ∈ Finset.range 129,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (293 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (293 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_293_suffix_zero :
    (∑ x ∈ Finset.range 129,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (293 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_293 :
    recurrence5A3Square.coeff 293 =
      -(((633845387183558878 * 10 ^ 70 +
        9199672629182752492799354246078231801479410285461333085054363829963082) * 10 ^ 70 +
        4645745548157280173767049389857032874154880073112961469131170896588404) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 294 = 129 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 4 +
      129 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_293_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_293_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_294_prefix_zero :
    (∑ x ∈ Finset.range 130,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (294 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (294 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_294_suffix_zero :
    (∑ x ∈ Finset.range 130,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (294 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_294 :
    recurrence5A3Square.coeff 294 =
      (((69806284288509420 * 10 ^ 70 +
        9560213536261259621804292352403006764608915082908526639799565365037631) * 10 ^ 70 +
        5722542392041327429791704155141829829559786060833095711999389927629977) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 295 = 130 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 3 +
      130 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_294_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_294_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_295_prefix_zero :
    (∑ x ∈ Finset.range 131,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (295 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (295 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_295_suffix_zero :
    (∑ x ∈ Finset.range 131,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (295 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_295 :
    recurrence5A3Square.coeff 295 =
      -(((6931057780659151 * 10 ^ 70 +
        2047498751079061699422210273318695820717479795422234758137255025608459) * 10 ^ 70 +
        1276194635041047070545349758317066266198193596051453396109224594500396) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 296 = 131 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 2 +
      131 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_295_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_295_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_296_prefix_zero :
    (∑ x ∈ Finset.range 132,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (296 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (296 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_296_suffix_zero :
    (∑ x ∈ Finset.range 132,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (296 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_296 :
    recurrence5A3Square.coeff 296 =
      (((614715863798566 * 10 ^ 70 +
        9494460432831125133625257992144350067828909366587238516187844586923137) * 10 ^ 70 +
        4446502443216354619274533839157310773473202480608701144151773461333427) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 297 = 132 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 1 +
      132 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_296_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_296_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_297_prefix_zero :
    (∑ x ∈ Finset.range 133,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (297 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (297 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_297_suffix_zero :
    (∑ x ∈ Finset.range 133,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (297 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_297 :
    recurrence5A3Square.coeff 297 =
      -(((48157068228405 * 10 ^ 70 +
        2701810787263081337791567371729838829306502890256082209462312606505834) * 10 ^ 70 +
        6075982186912188641820533800227722216405635993570993782061372713798580) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 298 = 133 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_297_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_297_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_298_prefix_zero :
    (∑ x ∈ Finset.range 134,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (298 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (298 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_298_suffix_zero :
    (∑ x ∈ Finset.range 134,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (298 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_298 :
    recurrence5A3Square.coeff 298 =
      (((3286827349838 * 10 ^ 70 +
        7225916710738763496753209552819384659514463355623220742938410489868177) * 10 ^ 70 +
        6627554129305416424788557909965027780118606618665512914729831862716444) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 299 = 134 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 31 +
      134 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_298_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_298_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_299_prefix_zero :
    (∑ x ∈ Finset.range 135,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (299 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (299 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_299_suffix_zero :
    (∑ x ∈ Finset.range 135,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (299 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_299 :
    recurrence5A3Square.coeff 299 =
      -(((192089079007 * 10 ^ 70 +
        1969338356489078373357762435889063287228861224309344759110154138833234) * 10 ^ 70 +
        9851493333403677501754571364466956906753167710673987151226724187473046) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 300 = 135 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 30 +
      135 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_299_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_299_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_300_prefix_zero :
    (∑ x ∈ Finset.range 136,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (300 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (300 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_300_suffix_zero :
    (∑ x ∈ Finset.range 136,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (300 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_300 :
    recurrence5A3Square.coeff 300 =
      (((9399708580 * 10 ^ 70 +
        9243121967758831171504504339871085030370588618559514721066881414170775) * 10 ^ 70 +
        5841757850458586364106618202119478896469971263380817028479068712264709) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 301 = 136 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 29 +
      136 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_300_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_300_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_301_prefix_zero :
    (∑ x ∈ Finset.range 137,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (301 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (301 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_301_suffix_zero :
    (∑ x ∈ Finset.range 137,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (301 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_301 :
    recurrence5A3Square.coeff 301 =
      -(((373755627 * 10 ^ 70 +
        8147347608710570688531307420560735247905797751427616003957751283687667) * 10 ^ 70 +
        3271776295228360451051967273530194858470183137401407991580911383983580) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 302 = 137 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 28 +
      137 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_301_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_301_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_302_prefix_zero :
    (∑ x ∈ Finset.range 138,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (302 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (302 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_302_suffix_zero :
    (∑ x ∈ Finset.range 138,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (302 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_302 :
    recurrence5A3Square.coeff 302 =
      (((11575777 * 10 ^ 70 +
        9814599602151425079968707566788103547489491208816553136990129267197878) * 10 ^ 70 +
        7629472352946818604818304923689918020150317870046300430677685955811321) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 303 = 138 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 27 +
      138 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_302_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_302_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_303_prefix_zero :
    (∑ x ∈ Finset.range 139,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (303 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (303 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_303_suffix_zero :
    (∑ x ∈ Finset.range 139,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (303 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_303 :
    recurrence5A3Square.coeff 303 =
      -(((261694 * 10 ^ 70 +
        4242677505594319933698639285251104172195265031434906540912523530194674) * 10 ^ 70 +
        4868512975174056605108806998111597416646769841043349044332357322010704) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 304 = 139 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 26 +
      139 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_303_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_303_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_304_prefix_zero :
    (∑ x ∈ Finset.range 140,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (304 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (304 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_304_suffix_zero :
    (∑ x ∈ Finset.range 140,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (304 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_304 :
    recurrence5A3Square.coeff 304 =
      (((3839 * 10 ^ 70 +
        5112050897449543659250277204485963495740658861527567230192019895921378) * 10 ^ 70 +
        8123978817539029311280896976948534750687766546308232012781742173484114) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 305 = 140 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 25 +
      140 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_304_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_304_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_305_prefix_zero :
    (∑ x ∈ Finset.range 141,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (305 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (305 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_305_suffix_zero :
    (∑ x ∈ Finset.range 141,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (305 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_305 :
    recurrence5A3Square.coeff 305 =
      -(((26 * 10 ^ 70 +
        4474039972910565838052603047929525215008676546368240032243117378540226) * 10 ^ 70 +
        5333815919415776002778368297253590920793285517254534228486580747151222) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 306 = 141 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 24 +
      141 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_305_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_305_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_306_prefix_zero :
    (∑ x ∈ Finset.range 142,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (306 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (306 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_306_suffix_zero :
    (∑ x ∈ Finset.range 142,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (306 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_306 :
    recurrence5A3Square.coeff 306 =
      -((937433506104227471393748967511953799678356274990619109995157688579351 * 10 ^ 70 +
        5803649828711483924039227039398330657924892131161670532901997506589812) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 307 = 142 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 23 +
      142 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_306_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_306_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_307_prefix_zero :
    (∑ x ∈ Finset.range 143,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (307 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (307 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_307_suffix_zero :
    (∑ x ∈ Finset.range 143,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (307 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_307 :
    recurrence5A3Square.coeff 307 =
      ((25993103418066985617822222331691928534433551155115168043121016655876 * 10 ^ 70 +
        3080628030693263157967154793434253987100698266568364240141677238991018) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 308 = 143 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 22 +
      143 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_307_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_307_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_308_prefix_zero :
    (∑ x ∈ Finset.range 144,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (308 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (308 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_308_suffix_zero :
    (∑ x ∈ Finset.range 144,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (308 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_308 :
    recurrence5A3Square.coeff 308 =
      -((79188936327513919866752083172769693709328446061569890576571553326 * 10 ^ 70 +
        5091902987070446415739796213514701779832864883322838339645867449733542) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 309 = 144 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 21 +
      144 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_308_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_308_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_309_prefix_zero :
    (∑ x ∈ Finset.range 145,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (309 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (309 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_309_suffix_zero :
    (∑ x ∈ Finset.range 145,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (309 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_309 :
    recurrence5A3Square.coeff 309 =
      -((625584334897587809044914756931576755282454844020749915023661940 * 10 ^ 70 +
        6324517527199252377178483028419406473470364763600115782971504372094742) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 310 = 145 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 20 +
      145 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_309_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_309_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_310_prefix_zero :
    (∑ x ∈ Finset.range 146,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (310 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (310 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_310_suffix_zero :
    (∑ x ∈ Finset.range 146,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (310 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_310 :
    recurrence5A3Square.coeff 310 =
      ((3535026303961947425808689691962913211671356946009334892524920 * 10 ^ 70 +
        8523945221329146445487948697198119371337803485295592256566049764889063) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 311 = 146 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 19 +
      146 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_310_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_310_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_311_prefix_zero :
    (∑ x ∈ Finset.range 147,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (311 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (311 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_311_suffix_zero :
    (∑ x ∈ Finset.range 147,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (311 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_311 :
    recurrence5A3Square.coeff 311 =
      ((2755404344530431856213457165457351666040131708548581351891 * 10 ^ 70 +
        8598431588982605150721058880833009242069264307139896895606750330963164) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 312 = 147 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 18 +
      147 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_311_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_311_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_312_prefix_zero :
    (∑ x ∈ Finset.range 148,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (312 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (312 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_312_suffix_zero :
    (∑ x ∈ Finset.range 148,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (312 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_312 :
    recurrence5A3Square.coeff 312 =
      -((47513713868037048200876314139975885644575788628414207444 * 10 ^ 70 +
        6884346110801441112941905109076140714773923712457380407245606534967605) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 313 = 148 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 17 +
      148 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_312_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_312_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_313_prefix_zero :
    (∑ x ∈ Finset.range 149,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (313 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (313 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_313_suffix_zero :
    (∑ x ∈ Finset.range 149,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (313 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_313 :
    recurrence5A3Square.coeff 313 =
      ((69952752977058559634686574631001659966011705678281149 * 10 ^ 70 +
        3026967103996441368854280329311313239307791317403279693782263545813322) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 314 = 149 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 16 +
      149 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_313_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_313_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_314_prefix_zero :
    (∑ x ∈ Finset.range 150,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (314 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (314 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_314_suffix_zero :
    (∑ x ∈ Finset.range 150,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (314 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_314 :
    recurrence5A3Square.coeff 314 =
      ((149909517188307078121606304917827767429010422933656 * 10 ^ 70 +
        8023817422379335841935952656127065771965346568761314816410766868616799) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 315 = 150 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 15 +
      150 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_314_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_314_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_315_prefix_zero :
    (∑ x ∈ Finset.range 151,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (315 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (315 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_315_suffix_zero :
    (∑ x ∈ Finset.range 151,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (315 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_315 :
    recurrence5A3Square.coeff 315 =
      -((602953141586486985811567593177822596796161489808 * 10 ^ 70 +
        5544246356046565852266195404404352770160150161739938281027403937616370) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 316 = 151 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 14 +
      151 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_315_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_315_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_316_prefix_zero :
    (∑ x ∈ Finset.range 152,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (316 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (316 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_316_suffix_zero :
    (∑ x ∈ Finset.range 152,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (316 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_316 :
    recurrence5A3Square.coeff 316 =
      ((808726760972795614457223427656192202615119131 * 10 ^ 70 +
        3116387326760182629529323290063713031863425233161848087531768478288812) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 317 = 152 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 13 +
      152 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_316_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_316_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_317_prefix_zero :
    (∑ x ∈ Finset.range 153,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (317 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (317 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_317_suffix_zero :
    (∑ x ∈ Finset.range 153,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (317 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_317 :
    recurrence5A3Square.coeff 317 =
      -((544505801333708889402628326164057376240395 * 10 ^ 70 +
        2897015696681291611822817939298425879357386504627771232557829632559702) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 318 = 153 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 12 +
      153 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_317_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_317_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_318_prefix_zero :
    (∑ x ∈ Finset.range 154,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (318 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (318 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_318_suffix_zero :
    (∑ x ∈ Finset.range 154,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (318 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_318 :
    recurrence5A3Square.coeff 318 =
      ((194964409002729381555431851899968787852 * 10 ^ 70 +
        2029935872165317440585893475663173733689245933194966321416325250165218) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 319 = 154 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 11 +
      154 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_318_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_318_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_319_prefix_zero :
    (∑ x ∈ Finset.range 155,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (319 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (319 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_319_suffix_zero :
    (∑ x ∈ Finset.range 155,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (319 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_319 :
    recurrence5A3Square.coeff 319 =
      -((36509083097803262436104081023829972 * 10 ^ 70 +
        3304129092544908279450638911405225780478534690342960433969123674111304) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 320 = 155 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 10 +
      155 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_319_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_319_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_320_prefix_zero :
    (∑ x ∈ Finset.range 156,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (320 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (320 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_320_suffix_zero :
    (∑ x ∈ Finset.range 156,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (320 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_320 :
    recurrence5A3Square.coeff 320 =
      ((3476408299107804651543331965290 * 10 ^ 70 +
        6071056074221424024120914087442208907376150534546815806931392027499127) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 321 = 156 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 9 +
      156 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_320_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_320_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_321_prefix_zero :
    (∑ x ∈ Finset.range 157,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (321 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (321 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_321_suffix_zero :
    (∑ x ∈ Finset.range 157,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (321 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_321 :
    recurrence5A3Square.coeff 321 =
      -((157836352738029978700968527 * 10 ^ 70 +
        9979867435919201664910418608124239477841212685064215038592859470768954) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 322 = 157 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 8 +
      157 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_321_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_321_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_322_prefix_zero :
    (∑ x ∈ Finset.range 158,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (322 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (322 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_322_suffix_zero :
    (∑ x ∈ Finset.range 158,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (322 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_322 :
    recurrence5A3Square.coeff 322 =
      ((3283541447647637420673 * 10 ^ 70 +
        9560151338221273107522710557452491861497630329586840292210065399626187) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 323 = 158 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 7 +
      158 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_322_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_322_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_323_prefix_zero :
    (∑ x ∈ Finset.range 159,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (323 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (323 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_323_suffix_zero :
    (∑ x ∈ Finset.range 159,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (323 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_323 :
    recurrence5A3Square.coeff 323 =
      -((27685621699707067 * 10 ^ 70 +
        7911923049586780301925861014365666926507197652274744283673423370550416) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 324 = 159 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 6 +
      159 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_323_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_323_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_324_prefix_zero :
    (∑ x ∈ Finset.range 160,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (324 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (324 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_324_suffix_zero :
    (∑ x ∈ Finset.range 160,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (324 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_324 :
    recurrence5A3Square.coeff 324 =
      ((92390336030 * 10 ^ 70 +
        4862674184059383380194461061521389401939160748837053599620802961376459) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 325 = 160 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 5 +
      160 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_324_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_324_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_325_prefix_zero :
    (∑ x ∈ Finset.range 161,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (325 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (325 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_325_suffix_zero :
    (∑ x ∈ Finset.range 161,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (325 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_325 :
    recurrence5A3Square.coeff 325 =
      -((92635 * 10 ^ 70 +
        1053503340676856800368102710160145593663195394413934181959839690562070) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 326 = 161 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 4 +
      161 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_325_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_325_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_326_prefix_zero :
    (∑ x ∈ Finset.range 162,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (326 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (326 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_326_suffix_zero :
    (∑ x ∈ Finset.range 162,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (326 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_326 :
    recurrence5A3Square.coeff 326 =
      (304717060906988227195731028688210479477394036078029906072821559728989 : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 327 = 162 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 3 +
      162 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_326_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_326_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_327_prefix_zero :
    (∑ x ∈ Finset.range 163,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (327 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (327 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_327_suffix_zero :
    (∑ x ∈ Finset.range 163,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (327 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_327 :
    recurrence5A3Square.coeff 327 =
      (-14966805652273259687694045024995476360256283255894241831875660 : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 328 = 163 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 2 +
      163 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_327_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_327_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_328_prefix_zero :
    (∑ x ∈ Finset.range 164,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (328 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (328 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_328_suffix_zero :
    (∑ x ∈ Finset.range 164,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (328 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_328 :
    recurrence5A3Square.coeff 328 =
      (199944508519179168873514110594451712887216908764160100 : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 329 = 164 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 1 +
      164 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_328_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_328_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
