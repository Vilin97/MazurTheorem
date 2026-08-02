/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupB2
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupA2
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 5 lookup certificate: B2A2 coefficient convolution

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
  recurrence5A2_coeff_0
  recurrence5A2_coeff_1
  recurrence5A2_coeff_2
  recurrence5A2_coeff_3
  recurrence5A2_coeff_4
  recurrence5A2_coeff_5
  recurrence5A2_coeff_6
  recurrence5A2_coeff_7
  recurrence5A2_coeff_8
  recurrence5A2_coeff_9
  recurrence5A2_coeff_10
  recurrence5A2_coeff_11
  recurrence5A2_coeff_12
  recurrence5A2_coeff_13
  recurrence5A2_coeff_14
  recurrence5A2_coeff_15
  recurrence5A2_coeff_16
  recurrence5A2_coeff_17
  recurrence5A2_coeff_18
  recurrence5A2_coeff_19
  recurrence5A2_coeff_20
  recurrence5A2_coeff_21
  recurrence5A2_coeff_22
  recurrence5A2_coeff_23
  recurrence5A2_coeff_24
  recurrence5A2_coeff_25
  recurrence5A2_coeff_26
  recurrence5A2_coeff_27
  recurrence5A2_coeff_28
  recurrence5A2_coeff_29
  recurrence5A2_coeff_30
  recurrence5A2_coeff_31
  recurrence5A2_coeff_32
  recurrence5A2_coeff_33
  recurrence5A2_coeff_34
  recurrence5A2_coeff_35
  recurrence5A2_coeff_36
  recurrence5A2_coeff_37
  recurrence5A2_coeff_38
  recurrence5A2_coeff_39
  recurrence5A2_coeff_40
  recurrence5A2_coeff_41
  recurrence5A2_coeff_42
  recurrence5A2_coeff_43
  recurrence5A2_coeff_44
  recurrence5A2_coeff_45

attribute [local simp]
  recurrence5A2_coeff_46
  recurrence5A2_coeff_47
  recurrence5A2_coeff_48
  recurrence5A2_coeff_49
  recurrence5A2_coeff_50
  recurrence5A2_coeff_51
  recurrence5A2_coeff_52
  recurrence5A2_coeff_53
  recurrence5A2_coeff_54
  recurrence5A2_coeff_55
  recurrence5A2_coeff_56
  recurrence5A2_coeff_57
  recurrence5A2_coeff_58
  recurrence5A2_coeff_59
  recurrence5A2_coeff_60
  recurrence5A2_coeff_61
  recurrence5A2_coeff_62
  recurrence5A2_coeff_63
  recurrence5A2_coeff_64
  recurrence5A2_coeff_65
  recurrence5A2_coeff_66
  recurrence5A2_coeff_67
  recurrence5A2_coeff_68
  recurrence5A2_coeff_69
  recurrence5A2_coeff_70
  recurrence5A2_coeff_71
  recurrence5A2_coeff_72
  recurrence5A2_coeff_73
  recurrence5A2_coeff_74
  recurrence5A2_coeff_75
  recurrence5A2_coeff_76
  recurrence5A2_coeff_77
  recurrence5A2_coeff_78
  recurrence5A2_coeff_79
  recurrence5A2_coeff_80
  recurrence5A2_coeff_81
  recurrence5A2_coeff_82
  recurrence5A2_coeff_83
  recurrence5A2_coeff_84
  recurrence5A2_coeff_85
  recurrence5A2_coeff_86
  recurrence5A2_coeff_87
  recurrence5A2_coeff_88
  recurrence5A2_coeff_89
  recurrence5A2_coeff_90
  recurrence5A2_coeff_91
  recurrence5A2_coeff_92
  recurrence5A2_coeff_93
  recurrence5A2_coeff_94
  recurrence5A2_coeff_95
  recurrence5A2_coeff_96
  recurrence5A2_coeff_97
  recurrence5A2_coeff_98
  recurrence5A2_coeff_99
  recurrence5A2_coeff_100
  recurrence5A2_coeff_101
  recurrence5A2_coeff_102
  recurrence5A2_coeff_103
  recurrence5A2_coeff_104
  recurrence5A2_coeff_105
  recurrence5A2_coeff_106
  recurrence5A2_coeff_107
  recurrence5A2_coeff_108
  recurrence5A2_coeff_109

attribute [local simp]
  recurrence5A2_coeff_110
  recurrence5A2_coeff_111
  recurrence5A2_coeff_112
  recurrence5A2_coeff_113
  recurrence5A2_coeff_114
  recurrence5A2_coeff_115
  recurrence5A2_coeff_116
  recurrence5A2_coeff_117
  recurrence5A2_coeff_118
  recurrence5A2_coeff_119
  recurrence5A2_coeff_120
  recurrence5A2_coeff_121
  recurrence5A2_coeff_122
  recurrence5A2_coeff_123
  recurrence5A2_coeff_124
  recurrence5A2_coeff_125
  recurrence5A2_coeff_126
  recurrence5A2_coeff_127
  recurrence5A2_coeff_128
  recurrence5A2_coeff_129
  recurrence5A2_coeff_130
  recurrence5A2_coeff_131
  recurrence5A2_coeff_132
  recurrence5A2_coeff_133
  recurrence5A2_coeff_134
  recurrence5A2_coeff_135
  recurrence5A2_coeff_136
  recurrence5A2_coeff_137
  recurrence5A2_coeff_138
  recurrence5A2_coeff_139
  recurrence5A2_coeff_140
  recurrence5A2_coeff_141
  recurrence5A2_coeff_142
  recurrence5A2_coeff_143
  recurrence5A2_coeff_144
  recurrence5A2_coeff_145
  recurrence5A2_coeff_146
  recurrence5A2_coeff_147
  recurrence5A2_coeff_148
  recurrence5A2_coeff_149
  recurrence5A2_coeff_150
  recurrence5A2_coeff_151
  recurrence5A2_coeff_152
  recurrence5A2_coeff_153
  recurrence5A2_coeff_154
  recurrence5A2_coeff_155
  recurrence5A2_coeff_156
  recurrence5A2_coeff_157
  recurrence5A2_coeff_158
  recurrence5A2_coeff_159
  recurrence5A2_coeff_160
  recurrence5A2_coeff_161
  recurrence5A2_coeff_162
  recurrence5A2_coeff_163
  recurrence5A2_coeff_164
  recurrence5A2_coeff_165
  recurrence5A2_coeff_166
  recurrence5A2_coeff_167
  recurrence5A2_coeff_168

private theorem recurrence5B2A2_coeff_219_prefix_zero :
    (∑ x ∈ Finset.range 51,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (219 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (219 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_219_suffix_zero :
    (∑ x ∈ Finset.range 74,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (219 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_219 :
    recurrence5B2A2.coeff 219 =
      -((((530975 * 10 ^ 70 +
        1583913439647590558377833772270013128095175191324612520387734681708307) * 10 ^ 70 +
        9238329278355407169425799811084120356671040823869552405587080683840328) * 10 ^ 70 +
        7210177616333028293281443541240369319812690945627741820469395286287987) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 220 = 51 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 31 +
      74 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_219_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_219_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_220_prefix_zero :
    (∑ x ∈ Finset.range 52,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (220 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (220 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_220_suffix_zero :
    (∑ x ∈ Finset.range 75,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (220 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_220 :
    recurrence5B2A2.coeff 220 =
      ((((250839 * 10 ^ 70 +
        0694481554313889114041669558887626980098142345881080227122080020300503) * 10 ^ 70 +
        8799467849572153220561627525030049196431085855012077732453882535566216) * 10 ^ 70 +
        7898208926272423403827013869424095765248322653950733393147999847234132) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 221 = 52 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 30 +
      75 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_220_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_220_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_221_prefix_zero :
    (∑ x ∈ Finset.range 53,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (221 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (221 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_221_suffix_zero :
    (∑ x ∈ Finset.range 76,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (221 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_221 :
    recurrence5B2A2.coeff 221 =
      -((((114394 * 10 ^ 70 +
        0374205316026831655880435026789183020026545129081066408487668569689701) * 10 ^ 70 +
        1809724259925097992970707562832659096803891110318231529929307707264668) * 10 ^ 70 +
        3806734200489339743603114845303744238748181592785166134274735625844021) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 222 = 53 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 29 +
      76 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_221_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_221_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_222_prefix_zero :
    (∑ x ∈ Finset.range 54,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (222 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (222 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_222_suffix_zero :
    (∑ x ∈ Finset.range 77,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (222 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_222 :
    recurrence5B2A2.coeff 222 =
      ((((50405 * 10 ^ 70 +
        1789915250656885706611686971592612034476267703035377070478447034074517) * 10 ^ 70 +
        6496531758566837174013856037616558185899144846180005241274478884215735) * 10 ^ 70 +
        1105615202865660554247526956407506702933034863343876617315344743228905) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 223 = 54 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 28 +
      77 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_222_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_222_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_223_prefix_zero :
    (∑ x ∈ Finset.range 55,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (223 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (223 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_223_suffix_zero :
    (∑ x ∈ Finset.range 78,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (223 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_223 :
    recurrence5B2A2.coeff 223 =
      -((((21478 * 10 ^ 70 +
        3532296225671984993982264504250406365000599038410380605624025030026958) * 10 ^ 70 +
        5867115150315066262662595610196832191389571123052583358418548511592726) * 10 ^ 70 +
        7797216956520927625537322981058731811793012439379574308211069257503493) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 224 = 55 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 27 +
      78 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_223_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_223_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_224_prefix_zero :
    (∑ x ∈ Finset.range 56,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (224 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (224 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_224_suffix_zero :
    (∑ x ∈ Finset.range 79,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (224 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_224 :
    recurrence5B2A2.coeff 224 =
      ((((8857 * 10 ^ 70 +
        4820514663306231121319458501805925761192239427904901941580820327063369) * 10 ^ 70 +
        1438170146181748299585318307715864032097557907820603499652512200757269) * 10 ^ 70 +
        5022822637834818759784500660666313103278501590843391675618312292693861) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 225 = 56 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 26 +
      79 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_224_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_224_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_225_prefix_zero :
    (∑ x ∈ Finset.range 57,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (225 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (225 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_225_suffix_zero :
    (∑ x ∈ Finset.range 80,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (225 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_225 :
    recurrence5B2A2.coeff 225 =
      -((((3536 * 10 ^ 70 +
        9448662557250830205050005773525237079621154213945916143332591825317364) * 10 ^ 70 +
        0434917527031938640181961562460765777797403505051121055652040928460965) * 10 ^ 70 +
        6232553368924936868851809543393682178279716824710715919643101990236721) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 226 = 57 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 25 +
      80 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_225_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_225_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_226_prefix_zero :
    (∑ x ∈ Finset.range 58,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (226 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (226 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_226_suffix_zero :
    (∑ x ∈ Finset.range 81,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (226 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_226 :
    recurrence5B2A2.coeff 226 =
      ((((1367 * 10 ^ 70 +
        8744950001247227276175296647041697114368642354873546733443471781682573) * 10 ^ 70 +
        9896523312113062909286338993905857776917883628744743734387435808021949) * 10 ^ 70 +
        3062301935919289996326771372086566711602628846208298449807457289739061) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 227 = 58 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 24 +
      81 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_226_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_226_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_227_prefix_zero :
    (∑ x ∈ Finset.range 59,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (227 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (227 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_227_suffix_zero :
    (∑ x ∈ Finset.range 82,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (227 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_227 :
    recurrence5B2A2.coeff 227 =
      -((((512 * 10 ^ 70 +
        2657260580378889481901705302438520273470841311321323260369141880733272) * 10 ^ 70 +
        1994958473471437051559685715868114845175837296127688601146348340408732) * 10 ^ 70 +
        6091155903852428622909243798475136636642111528150976480463410057251801) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 228 = 59 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 23 +
      82 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_227_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_227_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_228_prefix_zero :
    (∑ x ∈ Finset.range 60,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (228 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (228 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_228_suffix_zero :
    (∑ x ∈ Finset.range 83,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (228 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_228 :
    recurrence5B2A2.coeff 228 =
      ((((185 * 10 ^ 70 +
        6601517579119165324475187301398135610293960362943253593587297398708357) * 10 ^ 70 +
        9396006299700704833023694608753282246221349507026810328684692073889528) * 10 ^ 70 +
        9619726001101721637828924437796721032983850566127936781012883542708248) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 229 = 60 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 22 +
      83 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_228_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_228_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_229_prefix_zero :
    (∑ x ∈ Finset.range 61,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (229 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (229 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_229_suffix_zero :
    (∑ x ∈ Finset.range 84,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (229 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_229 :
    recurrence5B2A2.coeff 229 =
      -((((65 * 10 ^ 70 +
        0487344471479659779582661161266837039499920302484405984699510770890931) * 10 ^ 70 +
        3541174800887841806736090041455470292298471528668955317793319024575319) * 10 ^ 70 +
        7225884334906717198856208478286746982534945846744676961939373197025310) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 230 = 61 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 21 +
      84 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_229_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_229_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_230_prefix_zero :
    (∑ x ∈ Finset.range 62,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (230 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (230 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_230_suffix_zero :
    (∑ x ∈ Finset.range 85,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (230 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_230 :
    recurrence5B2A2.coeff 230 =
      ((((21 * 10 ^ 70 +
        9945133766868443155209535108767092236758097616700046937844466258251062) * 10 ^ 70 +
        2487056933552832713700932659578325898461276146935798484807900772577875) * 10 ^ 70 +
        3328232613511223814587828264434384331223742421786368436507327007277111) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 231 = 62 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 20 +
      85 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_230_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_230_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_231_prefix_zero :
    (∑ x ∈ Finset.range 63,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (231 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (231 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_231_suffix_zero :
    (∑ x ∈ Finset.range 86,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (231 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_231 :
    recurrence5B2A2.coeff 231 =
      -((((7 * 10 ^ 70 +
        1594140493827090860077933787713091852570082440737043377429994169301411) * 10 ^ 70 +
        3060310410405458165551717686525267078055238829054628862072160240213343) * 10 ^ 70 +
        8486602103117193505776320026685883200945733600398116754164295902032532) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 232 = 63 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 19 +
      86 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_231_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_231_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_232_prefix_zero :
    (∑ x ∈ Finset.range 64,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (232 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (232 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_232_suffix_zero :
    (∑ x ∈ Finset.range 87,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (232 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_232 :
    recurrence5B2A2.coeff 232 =
      ((((2 * 10 ^ 70 +
        2357806941555571245145102581066183034860411061324685100834158864544697) * 10 ^ 70 +
        6500307705183715307525018814136248651081992977624147655081092952679505) * 10 ^ 70 +
        9910739124020545401742041208646595240474448832905317183629342757553430) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 233 = 64 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 18 +
      87 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_232_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_232_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_233_prefix_zero :
    (∑ x ∈ Finset.range 65,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (233 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (233 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_233_suffix_zero :
    (∑ x ∈ Finset.range 88,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (233 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_233 :
    recurrence5B2A2.coeff 233 =
      -(((6665579155221294929502831657236343733364394741466717206451710260511379 * 10 ^ 70 +
        1821783324404012130005364510173367363698092588717410616856774169237141) * 10 ^ 70 +
        3958442871586153401703164971996958868360381790483768735099540319425550) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 234 = 65 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 17 +
      88 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_233_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_233_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_234_prefix_zero :
    (∑ x ∈ Finset.range 66,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (234 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (234 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_234_suffix_zero :
    (∑ x ∈ Finset.range 89,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (234 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_234 :
    recurrence5B2A2.coeff 234 =
      (((1883247780953175088001246684321410067425670425419937642462433475986523 * 10 ^ 70 +
        4509300821432393863986518928066172561004015274951922312752437058784159) * 10 ^ 70 +
        4174731818363224721647676277225155655957655527158421333492643704247860) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 235 = 66 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 16 +
      89 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_234_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_234_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_235_prefix_zero :
    (∑ x ∈ Finset.range 67,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (235 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (235 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_235_suffix_zero :
    (∑ x ∈ Finset.range 90,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (235 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_235 :
    recurrence5B2A2.coeff 235 =
      -(((498138867843524065796168545910680801639571137603641932618334187714571 * 10 ^ 70 +
        3207643911555663126316213150678865744547359758158323079401245001552244) * 10 ^ 70 +
        6281713336132790746346910152859118505923412258787978535791693973726585) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 236 = 67 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 15 +
      90 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_235_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_235_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_236_prefix_zero :
    (∑ x ∈ Finset.range 68,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (236 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (236 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_236_suffix_zero :
    (∑ x ∈ Finset.range 91,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (236 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_236 :
    recurrence5B2A2.coeff 236 =
      (((120505419255384200533740926893965940326860646894379797998351877334932 * 10 ^ 70 +
        2774464920212076950915942557286773158644044743423114219206238598828798) * 10 ^ 70 +
        0505921359245393188006150702385047493022933323005065718190223734210458) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 237 = 68 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 14 +
      91 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_236_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_236_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_237_prefix_zero :
    (∑ x ∈ Finset.range 69,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (237 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (237 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_237_suffix_zero :
    (∑ x ∈ Finset.range 92,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (237 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_237 :
    recurrence5B2A2.coeff 237 =
      -(((25207278322424259424944753408168465151556147068398464176602592189644 * 10 ^ 70 +
        1456165517245128692939633662460778365229455801954009880148240184262262) * 10 ^ 70 +
        3412722629541569690286094595561298466869069066863202239487491908852161) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 238 = 69 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 13 +
      92 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_237_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_237_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_238_prefix_zero :
    (∑ x ∈ Finset.range 70,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (238 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (238 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_238_suffix_zero :
    (∑ x ∈ Finset.range 93,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (238 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_238 :
    recurrence5B2A2.coeff 238 =
      (((3730362770996286728708203178300831699303936013146754904392329460377 * 10 ^ 70 +
        1938867961020888577697826593346366206649270871962928387284529891828184) * 10 ^ 70 +
        1210315671820443186485484507765402525045441060724006821009021625191007) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 239 = 70 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 12 +
      93 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_238_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_238_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_239_prefix_zero :
    (∑ x ∈ Finset.range 71,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (239 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (239 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_239_suffix_zero :
    (∑ x ∈ Finset.range 94,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (239 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_239 :
    recurrence5B2A2.coeff 239 =
      (((172560364708078597679666769609026273021537220896752291940879142027 * 10 ^ 70 +
        2282659760591154316220000738057639722326151012582278792829704368841101) * 10 ^ 70 +
        2517406183093685432586206900613942036169449000148107945418906447621362) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 240 = 71 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 11 +
      94 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_239_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_239_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_240_prefix_zero :
    (∑ x ∈ Finset.range 72,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (240 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (240 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_240_suffix_zero :
    (∑ x ∈ Finset.range 95,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (240 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_240 :
    recurrence5B2A2.coeff 240 =
      -(((485965886290382958143330189878921971858232336747115922304683477454 * 10 ^ 70 +
        7585576351275533603000069392938756364826291411852565881565078627006895) * 10 ^ 70 +
        1026732816404011124428412022510447262979776681940919105681684690886705) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 241 = 72 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 10 +
      95 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_240_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_240_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_241_prefix_zero :
    (∑ x ∈ Finset.range 73,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (241 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (241 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_241_suffix_zero :
    (∑ x ∈ Finset.range 96,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (241 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_241 :
    recurrence5B2A2.coeff 241 =
      (((295643460213274610368659701761927533498929323459623061950740928384 * 10 ^ 70 +
        6450247961643235197040186351185103179858844588246597937880945011462615) * 10 ^ 70 +
        9432100142095773935463322052592797451169577379960320677141182349925385) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 242 = 73 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 9 +
      96 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_241_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_241_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_242_prefix_zero :
    (∑ x ∈ Finset.range 74,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (242 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (242 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_242_suffix_zero :
    (∑ x ∈ Finset.range 97,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (242 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_242 :
    recurrence5B2A2.coeff 242 =
      -(((142549376238195577785213930330410817151225297886283492824255580580 * 10 ^ 70 +
        8374901012944888670663726031721319568612016692636031819708736403581095) * 10 ^ 70 +
        5164686734075272596556370229098119526193451656653883734196821219735783) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 243 = 74 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 8 +
      97 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_242_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_242_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_243_prefix_zero :
    (∑ x ∈ Finset.range 75,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (243 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (243 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_243_suffix_zero :
    (∑ x ∈ Finset.range 98,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (243 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_243 :
    recurrence5B2A2.coeff 243 =
      (((62814531529152182449967240788072106529540161378941046246399577613 * 10 ^ 70 +
        9743236349485835122430335721952858360848346491878779450696816664779784) * 10 ^ 70 +
        2437985593256616882973074529161054667567098301210708604084918326543064) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 244 = 75 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 7 +
      98 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_243_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_243_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_244_prefix_zero :
    (∑ x ∈ Finset.range 76,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (244 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (244 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_244_suffix_zero :
    (∑ x ∈ Finset.range 99,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (244 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_244 :
    recurrence5B2A2.coeff 244 =
      -(((26439500728245329113204740052112279002384579701839221169560896389 * 10 ^ 70 +
        1241157293641845060888242062917730580804902058894264865517913302474502) * 10 ^ 70 +
        7899283558737648446526157087698187012228031275890084898177753800214138) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 245 = 76 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 6 +
      99 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_244_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_244_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_245_prefix_zero :
    (∑ x ∈ Finset.range 77,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (245 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (245 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_245_suffix_zero :
    (∑ x ∈ Finset.range 100,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (245 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_245 :
    recurrence5B2A2.coeff 245 =
      (((10803429052527440619947240256292770453356188673131656461067347740 * 10 ^ 70 +
        8913072852607453047707103404428508941051464540466597614716937087639275) * 10 ^ 70 +
        7461699298643028428063613756545563512535011969581198382685514549114522) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 246 = 77 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 5 +
      100 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_245_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_245_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_246_prefix_zero :
    (∑ x ∈ Finset.range 78,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (246 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (246 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_246_suffix_zero :
    (∑ x ∈ Finset.range 101,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (246 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_246 :
    recurrence5B2A2.coeff 246 =
      -(((4308837264880448967181386711033547114838678758350593743534274111 * 10 ^ 70 +
        0630401653389809652504417765007942187579787047971398765870615076782144) * 10 ^ 70 +
        1280438791448059416589911837633021851989315693890997584330197705652589) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 247 = 78 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 4 +
      101 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_246_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_246_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_247_prefix_zero :
    (∑ x ∈ Finset.range 79,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (247 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (247 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_247_suffix_zero :
    (∑ x ∈ Finset.range 102,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (247 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_247 :
    recurrence5B2A2.coeff 247 =
      (((1679443055212983819206756931203745796858726190792904117099955952 * 10 ^ 70 +
        1320913514953015528734626287009981624507149509810800471247315676483535) * 10 ^ 70 +
        5298305430761041278423827136003198539934585310714866674452425683162826) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 248 = 79 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 3 +
      102 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_247_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_247_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_248_prefix_zero :
    (∑ x ∈ Finset.range 80,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (248 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (248 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_248_suffix_zero :
    (∑ x ∈ Finset.range 103,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (248 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_248 :
    recurrence5B2A2.coeff 248 =
      -(((639394923446396685197349632805449321771434489196075786755868850 * 10 ^ 70 +
        3659505039265725000717046499113512721094887451987013812485732945765181) * 10 ^ 70 +
        3554268850600399602750270487211307824896444754665168696343591497883579) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 249 = 80 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 2 +
      103 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_248_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_248_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_249_prefix_zero :
    (∑ x ∈ Finset.range 81,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (249 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (249 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_249_suffix_zero :
    (∑ x ∈ Finset.range 104,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (249 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_249 :
    recurrence5B2A2.coeff 249 =
      (((237496783106166543710460309757613148963158630021755830954489266 * 10 ^ 70 +
        3505141732651165897908618352569281876299237124625585123787785531404480) * 10 ^ 70 +
        1764856224327746319680796345187252845890870624008902969345157310676738) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 250 = 81 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 1 +
      104 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_249_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_249_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_250_prefix_zero :
    (∑ x ∈ Finset.range 82,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (250 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (250 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_250_suffix_zero :
    (∑ x ∈ Finset.range 105,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (250 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_250 :
    recurrence5B2A2.coeff 250 =
      -(((85927062407950356277259793388697398472524975351343262744425069 * 10 ^ 70 +
        2682412275412384619192168651169841720330041252564619415188037351877526) * 10 ^ 70 +
        1279180906363186489829396200959904144900435374328387986173944254563366) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 251 = 82 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_250_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_250_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_251_prefix_zero :
    (∑ x ∈ Finset.range 83,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (251 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (251 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_251_suffix_zero :
    (∑ x ∈ Finset.range 106,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (251 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_251 :
    recurrence5B2A2.coeff 251 =
      (((30221923382328825979650584469568712083618756807301993165930688 * 10 ^ 70 +
        0033689525959009571106770489202169402955749388298207331610649510166201) * 10 ^ 70 +
        1505581458942827477073357811222952970252703002505121967255194096469108) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 252 = 83 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 31 +
      106 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_251_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_251_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_252_prefix_zero :
    (∑ x ∈ Finset.range 84,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (252 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (252 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_252_suffix_zero :
    (∑ x ∈ Finset.range 107,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (252 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_252 :
    recurrence5B2A2.coeff 252 =
      -(((10309274316468050284123942211786342825379131544913230776436907 * 10 ^ 70 +
        2770333019370713136432686074435205149411737843389562100249495130928031) * 10 ^ 70 +
        6119001439011210804840712958834279194960842677085227287046792814553811) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 253 = 84 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 30 +
      107 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_252_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_252_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_253_prefix_zero :
    (∑ x ∈ Finset.range 85,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (253 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (253 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_253_suffix_zero :
    (∑ x ∈ Finset.range 108,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (253 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_253 :
    recurrence5B2A2.coeff 253 =
      (((3402119252768240625800735045288487602901886975319000309273047 * 10 ^ 70 +
        5089080682149186281867711475516903162306833893882844260018181243576452) * 10 ^ 70 +
        6633949964244902478065345064921701438209189037796567228723283381782065) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 254 = 85 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 29 +
      108 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_253_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_253_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_254_prefix_zero :
    (∑ x ∈ Finset.range 86,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (254 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (254 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_254_suffix_zero :
    (∑ x ∈ Finset.range 109,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (254 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_254 :
    recurrence5B2A2.coeff 254 =
      -(((1083379612426478434119669425877290860660727225267032328853834 * 10 ^ 70 +
        8878232037432717286163340048401074480844572622082590834661438572116511) * 10 ^ 70 +
        3260329097207595088678539877456023588323097662005921095883612274343679) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 255 = 86 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 28 +
      109 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_254_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_254_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_255_prefix_zero :
    (∑ x ∈ Finset.range 87,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (255 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (255 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_255_suffix_zero :
    (∑ x ∈ Finset.range 110,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (255 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_255 :
    recurrence5B2A2.coeff 255 =
      (((332140958321060725498672175790801871868045659614579088660396 * 10 ^ 70 +
        4341209243123626465392946773832010311458491580264514416617387551043132) * 10 ^ 70 +
        0994269060353427997411809430534419964460547725972130405387469569446756) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 256 = 87 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 27 +
      110 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_255_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_255_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_256_prefix_zero :
    (∑ x ∈ Finset.range 88,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (256 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (256 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_256_suffix_zero :
    (∑ x ∈ Finset.range 111,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (256 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_256 :
    recurrence5B2A2.coeff 256 =
      -(((97861201895994579973028583689532485625379427815607052418650 * 10 ^ 70 +
        7670434631173982641151628382069809088307549075314557208844580880351414) * 10 ^ 70 +
        5620859310546932623115849824568574924046326846184057523302049734201645) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 257 = 88 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 26 +
      111 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_256_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_256_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_257_prefix_zero :
    (∑ x ∈ Finset.range 89,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (257 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (257 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_257_suffix_zero :
    (∑ x ∈ Finset.range 112,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (257 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_257 :
    recurrence5B2A2.coeff 257 =
      (((27683991456314693602386712222123409444895059806681727075689 * 10 ^ 70 +
        2641578355106951656579876587515971806297947596388755155098717259341154) * 10 ^ 70 +
        5901798776977063036637412157621994906125240558648058673512968159785040) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 258 = 89 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 25 +
      112 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_257_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_257_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_258_prefix_zero :
    (∑ x ∈ Finset.range 90,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (258 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (258 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_258_suffix_zero :
    (∑ x ∈ Finset.range 113,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (258 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_258 :
    recurrence5B2A2.coeff 258 =
      -(((7518928474093799498384495709493626914041475950356784527885 * 10 ^ 70 +
        9295441001328248029754799935590093385066269330069865628346825159526240) * 10 ^ 70 +
        2854180846730188064568837343453174378415289958595463857112186301676564) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 259 = 90 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 24 +
      113 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_258_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_258_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_259_prefix_zero :
    (∑ x ∈ Finset.range 91,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (259 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (259 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_259_suffix_zero :
    (∑ x ∈ Finset.range 114,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (259 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_259 :
    recurrence5B2A2.coeff 259 =
      (((1961860312854302557855653924170303621835630998129334690592 * 10 ^ 70 +
        1610749514354254746568505047045518973376516199875481832001850119171909) * 10 ^ 70 +
        1936252360622869298062119422283227020085202447455491341739284674789191) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 260 = 91 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 23 +
      114 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_259_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_259_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_260_prefix_zero :
    (∑ x ∈ Finset.range 92,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (260 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (260 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_260_suffix_zero :
    (∑ x ∈ Finset.range 115,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (260 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_260 :
    recurrence5B2A2.coeff 260 =
      -(((492036659295090832839157985167246411077445455711767833228 * 10 ^ 70 +
        0311725118006532434443380244057138840306866467918260867032691358001576) * 10 ^ 70 +
        3417430787235555452816305704322220186436624794259310826848753055517870) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 261 = 92 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 22 +
      115 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_260_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_260_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_261_prefix_zero :
    (∑ x ∈ Finset.range 93,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (261 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (261 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_261_suffix_zero :
    (∑ x ∈ Finset.range 116,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (261 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_261 :
    recurrence5B2A2.coeff 261 =
      (((118490719589020428311796926051087849251875266544543382260 * 10 ^ 70 +
        5792826089824525522544742198567172107051215130600610380451003430787033) * 10 ^ 70 +
        3743360201325641112802311215486772589220248569109453611796445051888050) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 262 = 93 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 21 +
      116 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_261_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_261_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_262_prefix_zero :
    (∑ x ∈ Finset.range 94,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (262 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (262 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_262_suffix_zero :
    (∑ x ∈ Finset.range 117,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (262 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_262 :
    recurrence5B2A2.coeff 262 =
      -(((27266564589736588610633526820712358682452873257363336580 * 10 ^ 70 +
        3426257807061413723186954183897342970315017627271756386111443278210976) * 10 ^ 70 +
        8537397143239974339733257587760278435458738780934982535077867464831381) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 263 = 94 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 20 +
      117 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_262_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_262_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_263_prefix_zero :
    (∑ x ∈ Finset.range 95,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (263 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (263 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_263_suffix_zero :
    (∑ x ∈ Finset.range 118,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (263 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_263 :
    recurrence5B2A2.coeff 263 =
      (((5927569175545020954959425082996259790815529754734364540 * 10 ^ 70 +
        9056153770515183011167221378356094674855061312870362494931194016112009) * 10 ^ 70 +
        6511277955302957117738258335256134136789821547606643352091792689309509) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 264 = 95 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 19 +
      118 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_263_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_263_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_264_prefix_zero :
    (∑ x ∈ Finset.range 96,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (264 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (264 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_264_suffix_zero :
    (∑ x ∈ Finset.range 119,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (264 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_264 :
    recurrence5B2A2.coeff 264 =
      -(((1190539068268557506469439508543685100917782842780139410 * 10 ^ 70 +
        6328600796238098072803388608422818116375517138110839482305062755144384) * 10 ^ 70 +
        3401625825718203332649863758340592397110652117473531791838409629778010) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 265 = 96 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 18 +
      119 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_264_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_264_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_265_prefix_zero :
    (∑ x ∈ Finset.range 97,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (265 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (265 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_265_suffix_zero :
    (∑ x ∈ Finset.range 120,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (265 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_265 :
    recurrence5B2A2.coeff 265 =
      (((211499173867479759513932886138703088992748535911279693 * 10 ^ 70 +
        4490345446165184352267342142875407554202225536624818096196474888098675) * 10 ^ 70 +
        2938404927629361397758744380587931977953253549107576940038814405947722) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 266 = 97 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 17 +
      120 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_265_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_265_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_266_prefix_zero :
    (∑ x ∈ Finset.range 98,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (266 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (266 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_266_suffix_zero :
    (∑ x ∈ Finset.range 121,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (266 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_266 :
    recurrence5B2A2.coeff 266 =
      -(((29915210640957375034475489490731234631638163444320786 * 10 ^ 70 +
        3962106040592574512336390628362544898165876541824420793373635358525463) * 10 ^ 70 +
        2001949468011667787462398510267368171745938442478464313555255228386143) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 267 = 98 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 16 +
      121 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_266_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_266_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_267_prefix_zero :
    (∑ x ∈ Finset.range 99,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (267 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (267 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_267_suffix_zero :
    (∑ x ∈ Finset.range 122,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (267 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_267 :
    recurrence5B2A2.coeff 267 =
      (((2062991799655088139824614245656942988376023504051029 * 10 ^ 70 +
        4621420925764115979079958420558080416581464290550373228411400483111367) * 10 ^ 70 +
        7880995171339988647433767003244234674220717980693493884442627956841368) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 268 = 99 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 15 +
      122 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_267_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_267_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_268_prefix_zero :
    (∑ x ∈ Finset.range 100,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (268 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (268 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_268_suffix_zero :
    (∑ x ∈ Finset.range 123,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (268 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_268 :
    recurrence5B2A2.coeff 268 =
      (((570346730709804304803393194492601112949357132398338 * 10 ^ 70 +
        3022126195186535315769666777515122561240237539158554636128539618023887) * 10 ^ 70 +
        9607127212483665680196357312318518942562669784954068806583155240550517) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 269 = 100 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 14 +
      123 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_268_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_268_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_269_prefix_zero :
    (∑ x ∈ Finset.range 101,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (269 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (269 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_269_suffix_zero :
    (∑ x ∈ Finset.range 124,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (269 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_269 :
    recurrence5B2A2.coeff 269 =
      -(((309932909268576524893590413597028450077097737735729 * 10 ^ 70 +
        0040108871614009906517313205010412445322912073584775595102488321710467) * 10 ^ 70 +
        6107588309591530511008004918375983928597947673780881667904293103830333) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 270 = 101 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 13 +
      124 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_269_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_269_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_270_prefix_zero :
    (∑ x ∈ Finset.range 102,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (270 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (270 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_270_suffix_zero :
    (∑ x ∈ Finset.range 125,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (270 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_270 :
    recurrence5B2A2.coeff 270 =
      (((89658392556814853993168259553779947842726887727978 * 10 ^ 70 +
        8083803589795488958007387462343680657514178535701779929803136502856628) * 10 ^ 70 +
        3577138132417575190905840408328137419703902788514938664124562843617610) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 271 = 102 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 12 +
      125 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_270_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_270_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_271_prefix_zero :
    (∑ x ∈ Finset.range 103,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (271 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (271 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_271_suffix_zero :
    (∑ x ∈ Finset.range 126,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (271 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_271 :
    recurrence5B2A2.coeff 271 =
      -(((18983935569384532765406711098317335955530109655927 * 10 ^ 70 +
        4313120012479795261463072549582063067777090883275431874988569730734114) * 10 ^ 70 +
        0279557352293010188889648230786707621734411850579639835715598187829080) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 272 = 103 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 11 +
      126 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_271_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_271_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_272_prefix_zero :
    (∑ x ∈ Finset.range 104,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (272 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (272 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_272_suffix_zero :
    (∑ x ∈ Finset.range 127,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (272 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_272 :
    recurrence5B2A2.coeff 272 =
      (((2905028197314547830104673451939925846951164258988 * 10 ^ 70 +
        9214122470098222799250343889545101522920398238358914652934472463731695) * 10 ^ 70 +
        1168184976023844703657982551553721601532112481538353543093415982116184) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 273 = 104 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 10 +
      127 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_272_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_272_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_273_prefix_zero :
    (∑ x ∈ Finset.range 105,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (273 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (273 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_273_suffix_zero :
    (∑ x ∈ Finset.range 128,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (273 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_273 :
    recurrence5B2A2.coeff 273 =
      -(((222112549410310889370181964919479021555671427849 * 10 ^ 70 +
        2864759217432064995361124205969882024733342649818535417686212444068960) * 10 ^ 70 +
        6754322549099066542676020076714007297828812058188194853535491284580862) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 274 = 105 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 9 +
      128 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_273_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_273_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_274_prefix_zero :
    (∑ x ∈ Finset.range 106,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (274 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (274 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_274_suffix_zero :
    (∑ x ∈ Finset.range 129,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (274 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_274 :
    recurrence5B2A2.coeff 274 =
      -(((39262684405389339298568696535596467835046520387 * 10 ^ 70 +
        9753978189260795368483681235859157479921042119447105254484201977773981) * 10 ^ 70 +
        9069989651568322976245375341377187680465356274348323141245832628870026) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 275 = 106 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 8 +
      129 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_274_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_274_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_275_prefix_zero :
    (∑ x ∈ Finset.range 107,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (275 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (275 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_275_suffix_zero :
    (∑ x ∈ Finset.range 130,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (275 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_275 :
    recurrence5B2A2.coeff 275 =
      (((20819765473080538622478521354775565345639167032 * 10 ^ 70 +
        7928493113868717899224103073589581978394876107012428902730302005963724) * 10 ^ 70 +
        1590517609445855301106532107856571811912807657755228969181060417275286) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 276 = 107 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 7 +
      130 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_275_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_275_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_276_prefix_zero :
    (∑ x ∈ Finset.range 108,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (276 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (276 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_276_suffix_zero :
    (∑ x ∈ Finset.range 131,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (276 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_276 :
    recurrence5B2A2.coeff 276 =
      -(((5125457772334551163491610947290284967832311470 * 10 ^ 70 +
        1929281403547747405119105202043754603591658700872704867609677906718981) * 10 ^ 70 +
        2009326844725882325404227129285289299355090107542102283195167078003084) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 277 = 108 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 6 +
      131 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_276_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_276_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_277_prefix_zero :
    (∑ x ∈ Finset.range 109,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (277 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (277 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_277_suffix_zero :
    (∑ x ∈ Finset.range 132,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (277 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_277 :
    recurrence5B2A2.coeff 277 =
      (((876872250473221631465107192805622129787019259 * 10 ^ 70 +
        8039066045371660819329969114679088402097042282051619227298068396410277) * 10 ^ 70 +
        4806774896794214106473955242242295858180716560995765836813132225211218) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 278 = 109 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 5 +
      132 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_277_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_277_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_278_prefix_zero :
    (∑ x ∈ Finset.range 110,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (278 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (278 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_278_suffix_zero :
    (∑ x ∈ Finset.range 133,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (278 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_278 :
    recurrence5B2A2.coeff 278 =
      -(((105720893153304940489914241451832779147105319 * 10 ^ 70 +
        4963486498586317020234713516519379022885996348487399750695043385780603) * 10 ^ 70 +
        7107705344678786305486464064167843654743740082523172908196105765430467) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 279 = 110 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 4 +
      133 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_278_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_278_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_279_prefix_zero :
    (∑ x ∈ Finset.range 111,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (279 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (279 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_279_suffix_zero :
    (∑ x ∈ Finset.range 134,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (279 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_279 :
    recurrence5B2A2.coeff 279 =
      (((7033242771974435706155101851726278864044327 * 10 ^ 70 +
        0200689231936082725598732231119877352988631653516588747977181778524535) * 10 ^ 70 +
        2878556120606392794965761342669650454783951896880667731354713912127732) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 280 = 111 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 3 +
      134 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_279_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_279_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_280_prefix_zero :
    (∑ x ∈ Finset.range 112,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (280 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (280 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_280_suffix_zero :
    (∑ x ∈ Finset.range 135,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (280 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_280 :
    recurrence5B2A2.coeff 280 =
      (((373958664240267389471868339179548746737311 * 10 ^ 70 +
        3587761360250780002492686705056323029763111616914468880351670842816343) * 10 ^ 70 +
        1706670307393534510574274821029588708626775126607027510563277685708422) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 281 = 112 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 2 +
      135 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_280_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_280_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_281_prefix_zero :
    (∑ x ∈ Finset.range 113,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (281 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (281 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_281_suffix_zero :
    (∑ x ∈ Finset.range 136,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (281 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_281 :
    recurrence5B2A2.coeff 281 =
      -(((186490993394568856022330589104267954085538 * 10 ^ 70 +
        8248876194877017988874991701989385966205984654620606835385646393001910) * 10 ^ 70 +
        6008618544440692991104316637264999732718076772056695734797043268670606) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 282 = 113 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 1 +
      136 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_281_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_281_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_282_prefix_zero :
    (∑ x ∈ Finset.range 114,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (282 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (282 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_282_suffix_zero :
    (∑ x ∈ Finset.range 137,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (282 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_282 :
    recurrence5B2A2.coeff 282 =
      (((29296086683926463377784380778165498467491 * 10 ^ 70 +
        8587829749294154973720668880667169353242441376410205798386656539232467) * 10 ^ 70 +
        0630974073672283446648080280102336441429956976113046576378659372051206) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 283 = 114 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_282_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_282_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_283_prefix_zero :
    (∑ x ∈ Finset.range 115,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (283 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (283 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_283_suffix_zero :
    (∑ x ∈ Finset.range 138,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (283 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_283 :
    recurrence5B2A2.coeff 283 =
      -(((2746785710828030553469613246600574383622 * 10 ^ 70 +
        7763654469001462819072542752030146033387730196877062498642504461098033) * 10 ^ 70 +
        5113058896116866193637523465877694927519635412787982141438243410900343) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 284 = 115 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 31 +
      138 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_283_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_283_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_284_prefix_zero :
    (∑ x ∈ Finset.range 116,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (284 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (284 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_284_suffix_zero :
    (∑ x ∈ Finset.range 139,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (284 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_284 :
    recurrence5B2A2.coeff 284 =
      (((130924417699129453801473588865520047392 * 10 ^ 70 +
        5802957294885591355402124912301927708682148179173921222357175061231614) * 10 ^ 70 +
        4936897146524510813646133257432166505598051300794782717574204747245656) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 285 = 116 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 30 +
      139 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_284_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_284_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_285_prefix_zero :
    (∑ x ∈ Finset.range 117,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (285 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (285 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_285_suffix_zero :
    (∑ x ∈ Finset.range 140,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (285 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_285 :
    recurrence5B2A2.coeff 285 =
      (((3965893425535601471256735459278849134 * 10 ^ 70 +
        4639029031893516242006715481295233403663797822851082920217847698266474) * 10 ^ 70 +
        9606898777779999695081990809968454616465084440088598089964132146731031) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 286 = 117 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 29 +
      140 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_285_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_285_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_286_prefix_zero :
    (∑ x ∈ Finset.range 118,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (286 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (286 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_286_suffix_zero :
    (∑ x ∈ Finset.range 141,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (286 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_286 :
    recurrence5B2A2.coeff 286 =
      -(((1238969080768191122760154553249044088 * 10 ^ 70 +
        0857259802732465062618708632255322162481340445558468068066274360745792) * 10 ^ 70 +
        8825576294835545508982475629954077447686622550406887816673579811422758) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 287 = 118 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 28 +
      141 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_286_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_286_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_287_prefix_zero :
    (∑ x ∈ Finset.range 119,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (287 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (287 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_287_suffix_zero :
    (∑ x ∈ Finset.range 142,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (287 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_287 :
    recurrence5B2A2.coeff 287 =
      (((98911316189016584878835957397914841 * 10 ^ 70 +
        0868695474178390582677436129352757890582530364898166046037724626159498) * 10 ^ 70 +
        1754140552231959093877804833083544815883659734615039348126533208093309) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 288 = 119 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 27 +
      142 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_287_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_287_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_288_prefix_zero :
    (∑ x ∈ Finset.range 120,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (288 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (288 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_288_suffix_zero :
    (∑ x ∈ Finset.range 143,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (288 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_288 :
    recurrence5B2A2.coeff 288 =
      -(((3418531481690314754616335439655031 * 10 ^ 70 +
        1725295945815366776655072866764330650709948099761692214118532204898680) * 10 ^ 70 +
        3769459548255205336860431153299350574042188837538857227905769851796148) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 289 = 120 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 26 +
      143 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_288_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_288_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_289_prefix_zero :
    (∑ x ∈ Finset.range 121,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (289 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (289 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_289_suffix_zero :
    (∑ x ∈ Finset.range 144,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (289 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_289 :
    recurrence5B2A2.coeff 289 =
      -(((25441081492572976431696160183533 * 10 ^ 70 +
        7938094946131321332678791641928349178420971027911062773135999387838950) * 10 ^ 70 +
        3465324896848559238823719639009030723160753185580299741307884522407957) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 290 = 121 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 25 +
      144 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_289_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_289_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_290_prefix_zero :
    (∑ x ∈ Finset.range 122,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (290 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (290 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_290_suffix_zero :
    (∑ x ∈ Finset.range 145,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (290 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_290 :
    recurrence5B2A2.coeff 290 =
      (((5770134086973797216486593486205 * 10 ^ 70 +
        7465421029297117938563487459671308261157592764285547793425658952838368) * 10 ^ 70 +
        6276488936389699612494543542143370919283048120296792918174387181546713) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 291 = 122 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 24 +
      145 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_290_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_290_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_291_prefix_zero :
    (∑ x ∈ Finset.range 123,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (291 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (291 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_291_suffix_zero :
    (∑ x ∈ Finset.range 146,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (291 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_291 :
    recurrence5B2A2.coeff 291 =
      -(((100154273231761299822014373038 * 10 ^ 70 +
        9264596759777107366046275217556956933587005253741831178489784189881915) * 10 ^ 70 +
        6875836173140190161884566838323870565139024477052223430052898918966231) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 292 = 123 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 23 +
      146 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_291_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_291_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_292_prefix_zero :
    (∑ x ∈ Finset.range 124,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (292 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (292 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_292_suffix_zero :
    (∑ x ∈ Finset.range 147,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (292 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_292 :
    recurrence5B2A2.coeff 292 =
      -(((2133649183432840179104113082 * 10 ^ 70 +
        7079050716536349630830920983173740912484978696501440177363499412958291) * 10 ^ 70 +
        4864837863257695785596628727869332295220539062198247831342236209689909) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 293 = 124 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 22 +
      147 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_292_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_292_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_293_prefix_zero :
    (∑ x ∈ Finset.range 125,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (293 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (293 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_293_suffix_zero :
    (∑ x ∈ Finset.range 148,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (293 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_293 :
    recurrence5B2A2.coeff 293 =
      (((18541283629260281767678209 * 10 ^ 70 +
        6667756970846470099413525897134361509549206709269203243161336657791063) * 10 ^ 70 +
        7496101902523180746660970508100397640241648044822561060232475535187377) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 294 = 125 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 21 +
      148 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_293_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_293_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_294_prefix_zero :
    (∑ x ∈ Finset.range 126,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (294 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (294 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_294_suffix_zero :
    (∑ x ∈ Finset.range 149,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (294 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_294 :
    recurrence5B2A2.coeff 294 =
      (((329468208324438338095842 * 10 ^ 70 +
        9044502744403643135359291144783414248907957247164936142182121379759823) * 10 ^ 70 +
        7238541285484104620664602489644853363710766240537849124301198344353847) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 295 = 126 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 20 +
      149 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_294_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_294_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_295_prefix_zero :
    (∑ x ∈ Finset.range 127,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (295 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (295 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_295_suffix_zero :
    (∑ x ∈ Finset.range 150,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (295 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_295 :
    recurrence5B2A2.coeff 295 =
      (((342812937641577556717 * 10 ^ 70 +
        7916809820600511767343440007742902207315572239099509961003240638323215) * 10 ^ 70 +
        4307617681193223759361004609152689971926870583272873931604815988910955) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 296 = 127 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 19 +
      150 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_295_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_295_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_296_prefix_zero :
    (∑ x ∈ Finset.range 128,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (296 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (296 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_296_suffix_zero :
    (∑ x ∈ Finset.range 151,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (296 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_296 :
    recurrence5B2A2.coeff 296 =
      -(((9156215933587646054 * 10 ^ 70 +
        1666582720780490198619037390903496023548584506381775182717569622428557) * 10 ^ 70 +
        0992108421654928179717547583402918840829636630541562194308891799465548) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 297 = 128 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 18 +
      151 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_296_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_296_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_297_prefix_zero :
    (∑ x ∈ Finset.range 129,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (297 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (297 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_297_suffix_zero :
    (∑ x ∈ Finset.range 152,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (297 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_297 :
    recurrence5B2A2.coeff 297 =
      -(((26106832689553933 * 10 ^ 70 +
        7144562895246770695356332135708149539058674813895884646294584505193080) * 10 ^ 70 +
        3027102289897543516664065505695243900345246272731775535653961495615101) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 298 = 129 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 17 +
      152 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_297_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_297_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_298_prefix_zero :
    (∑ x ∈ Finset.range 130,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (298 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (298 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_298_suffix_zero :
    (∑ x ∈ Finset.range 153,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (298 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_298 :
    recurrence5B2A2.coeff 298 =
      (((69767845388213 * 10 ^ 70 +
        6644482115409788371717600076974473172635171246946249255174807100929932) * 10 ^ 70 +
        5303890182844471334963719465525700722556648372972374325171594869444724) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 299 = 130 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 16 +
      153 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_298_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_298_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_299_prefix_zero :
    (∑ x ∈ Finset.range 131,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (299 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (299 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_299_suffix_zero :
    (∑ x ∈ Finset.range 154,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (299 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_299 :
    recurrence5B2A2.coeff 299 =
      (((249592944777 * 10 ^ 70 +
        0050549756340242297351827664931643906412283331538853471621874912718010) * 10 ^ 70 +
        0465867754804388644215096810639985899520407794504130741388441370101562) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 300 = 131 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 15 +
      154 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_299_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_299_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_300_prefix_zero :
    (∑ x ∈ Finset.range 132,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (300 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (300 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_300_suffix_zero :
    (∑ x ∈ Finset.range 155,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (300 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_300 :
    recurrence5B2A2.coeff 300 =
      -(((274547431 * 10 ^ 70 +
        3019973732823298254525630160123991642323432800167304953470598082113743) * 10 ^ 70 +
        5311600372262453755205955524585834902612492963466547935644640709875785) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 301 = 132 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 14 +
      155 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_300_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_300_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_301_prefix_zero :
    (∑ x ∈ Finset.range 133,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (301 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (301 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_301_suffix_zero :
    (∑ x ∈ Finset.range 156,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (301 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_301 :
    recurrence5B2A2.coeff 301 =
      -(((835523 * 10 ^ 70 +
        3441113787610924166590955803341487117190854827543699307487171841823094) * 10 ^ 70 +
        4524962716414640947062992427916157479463715306146005277482836298429033) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 302 = 133 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 13 +
      156 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_301_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_301_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_302_prefix_zero :
    (∑ x ∈ Finset.range 134,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (302 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (302 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_302_suffix_zero :
    (∑ x ∈ Finset.range 157,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (302 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_302 :
    recurrence5B2A2.coeff 302 =
      (((716 * 10 ^ 70 +
        4056784152547972228883930953093045850393397315573604614987832541848712) * 10 ^ 70 +
        2236350793589804347422294658184851454456371704540689398578012560956754) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 303 = 134 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 12 +
      157 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_302_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_302_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_303_prefix_zero :
    (∑ x ∈ Finset.range 135,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (303 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (303 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_303_suffix_zero :
    (∑ x ∈ Finset.range 158,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (303 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_303 :
    recurrence5B2A2.coeff 303 =
      ((6228833468222671428096083929294412140437961314865294245999874386108354 * 10 ^ 70 +
        7044394739754390396460460549942754713086916952235117081060880568780707) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 304 = 135 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 11 +
      158 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_303_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_303_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_304_prefix_zero :
    (∑ x ∈ Finset.range 136,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (304 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (304 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_304_suffix_zero :
    (∑ x ∈ Finset.range 159,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (304 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_304 :
    recurrence5B2A2.coeff 304 =
      -((3544871320606423618479423407013075034496740785326755629295286214506 * 10 ^ 70 +
        4450368033197522372104841852584977408585013448218141051552391715893320) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 305 = 136 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 10 +
      159 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_304_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_304_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_305_prefix_zero :
    (∑ x ∈ Finset.range 137,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (305 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (305 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_305_suffix_zero :
    (∑ x ∈ Finset.range 160,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (305 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_305 :
    recurrence5B2A2.coeff 305 =
      -((248035537963423676221139303615584555957625691632732007928294332 * 10 ^ 70 +
        4539277715089492376673864947345631939155406331232707818432262705411145) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 306 = 137 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 9 +
      160 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_305_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_305_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_306_prefix_zero :
    (∑ x ∈ Finset.range 138,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (306 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (306 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_306_suffix_zero :
    (∑ x ∈ Finset.range 161,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (306 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_306 :
    recurrence5B2A2.coeff 306 =
      ((86163334488302975181652556560931123346225513621233649275808 * 10 ^ 70 +
        7152060216315784783809965712869260501892100260124140515508024485849469) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 307 = 138 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 8 +
      161 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_306_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_306_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_307_prefix_zero :
    (∑ x ∈ Finset.range 139,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (307 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (307 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_307_suffix_zero :
    (∑ x ∈ Finset.range 162,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (307 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_307 :
    recurrence5B2A2.coeff 307 =
      -((484599020097519415582196237757240350860246972293553063 * 10 ^ 70 +
        5377189312542562920801002769518892029347944836431368844202816234598734) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 308 = 139 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 7 +
      162 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_307_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_307_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_308_prefix_zero :
    (∑ x ∈ Finset.range 140,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (308 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (308 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_308_suffix_zero :
    (∑ x ∈ Finset.range 163,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (308 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_308 :
    recurrence5B2A2.coeff 308 =
      -((59812810585017996755703020988696538710926088559915 * 10 ^ 70 +
        5302833920980037724448451634431256146126709447549407157805989182675097) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 309 = 140 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 6 +
      163 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_308_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_308_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_309_prefix_zero :
    (∑ x ∈ Finset.range 141,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (309 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (309 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_309_suffix_zero :
    (∑ x ∈ Finset.range 164,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (309 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_309 :
    recurrence5B2A2.coeff 309 =
      ((198893018092584724685487446450818869218745331 * 10 ^ 70 +
        5395305356765759464626305932047799746502258139002691720381019885014656) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 310 = 141 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 5 +
      164 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_309_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_309_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_310_prefix_zero :
    (∑ x ∈ Finset.range 142,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (310 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (310 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_310_suffix_zero :
    (∑ x ∈ Finset.range 165,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (310 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_310 :
    recurrence5B2A2.coeff 310 =
      ((492095854115531530349170742184231006481 * 10 ^ 70 +
        1077305512406491655539713949402908190411750861599552594631660962808680) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 311 = 142 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 4 +
      165 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_310_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_310_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_311_prefix_zero :
    (∑ x ∈ Finset.range 143,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (311 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (311 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_311_suffix_zero :
    (∑ x ∈ Finset.range 166,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (311 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_311 :
    recurrence5B2A2.coeff 311 =
      -((234981734525166934828006398828847 * 10 ^ 70 +
        8121316584133410506612619527487376631758534878329151805918808942645447) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 312 = 143 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 3 +
      166 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_311_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_311_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_312_prefix_zero :
    (∑ x ∈ Finset.range 144,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (312 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (312 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_312_suffix_zero :
    (∑ x ∈ Finset.range 167,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (312 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_312 :
    recurrence5B2A2.coeff 312 =
      -((15276566442046409432972861 * 10 ^ 70 +
        9634217502618996611424382561845923613809346094197154074412006608330787) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 313 = 144 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 2 +
      167 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_312_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_312_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_313_prefix_zero :
    (∑ x ∈ Finset.range 145,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (313 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (313 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_313_suffix_zero :
    (∑ x ∈ Finset.range 168,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (313 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_313 :
    recurrence5B2A2.coeff 313 =
      ((304685030578759320 * 10 ^ 70 +
        6174965024932678405343457376857058124353403007395935064774625125153199) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 314 = 145 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 1 +
      168 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_313_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_313_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
