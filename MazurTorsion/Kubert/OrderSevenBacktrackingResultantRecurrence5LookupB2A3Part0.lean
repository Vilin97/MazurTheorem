/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupB2
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupA3
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 5 lookup certificate: B2A3 coefficient convolution

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

attribute [local simp]
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

attribute [local simp]
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

theorem recurrence5B2A3_coeff_0 :
    recurrence5B2A3.coeff 0 =
      ((48 * 10 ^ 70 +
        5488553144903175665120206907073313912963917670213803256214235831195648) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 1 = 0 +
    1 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 1 = 1 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5B2A3_coeff_1 :
    recurrence5B2A3.coeff 1 =
      -((71860 * 10 ^ 70 +
        8748545756422161630689437710719134893650026902786383886928396775923328) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 2 = 0 +
    2 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 2 = 2 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5B2A3_coeff_2 :
    recurrence5B2A3.coeff 2 =
      ((475601633 * 10 ^ 70 +
        3464333537908235487004177863233805069182808753985003838970975213097312) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 3 = 0 +
    3 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5B2A3_coeff_3 :
    recurrence5B2A3.coeff 3 =
      -((1726962002788 * 10 ^ 70 +
        1292005783711536055456037897297303770959527799884135381984868578485976) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 4 = 0 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5B2A3_coeff_4 :
    recurrence5B2A3.coeff 4 =
      ((3226649198797744 * 10 ^ 70 +
        9836947142640043571596963739722694942547379738929405533485777398986784) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 5 = 0 +
    5 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 5 = 5 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5B2A3_coeff_5 :
    recurrence5B2A3.coeff 5 =
      -((3433950756504242786 * 10 ^ 70 +
        9376543253039455722708020998316686154759799587995090404015814059529288) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 6 = 0 +
    6 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 6 = 6 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5B2A3_coeff_6 :
    recurrence5B2A3.coeff 6 =
      ((2316982640853859198376 * 10 ^ 70 +
        6656675301293842105653448829989713659688758452855734431287952069070576) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 7 = 0 +
    7 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5B2A3_coeff_7 :
    recurrence5B2A3.coeff 7 =
      -((846522830234174383129751 * 10 ^ 70 +
        0094039609403273889180900424854522460193515952341276519887551685571304) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 8 = 0 +
    8 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 8 = 8 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5B2A3_coeff_8 :
    recurrence5B2A3.coeff 8 =
      ((1814661901860155652825507 * 10 ^ 70 +
        3466322806800694012098968174000537739943418100225574623866423504917484) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 9 = 0 +
    9 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 9 = 9 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5B2A3_coeff_9 :
    recurrence5B2A3.coeff 9 =
      ((191262421756386795043687807210 * 10 ^ 70 +
        6796811068091512270947097596984183818736119911780521578635581540912396) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 10 = 0 +
    10 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 10 = 10 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5B2A3_coeff_10 :
    recurrence5B2A3.coeff 10 =
      -((143508277394368334398215557935094 * 10 ^ 70 +
        1025754956157065888830120597734869484363685418683659569053675401311704) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 11 = 0 +
    11 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 11 = 11 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5B2A3_coeff_11 :
    recurrence5B2A3.coeff 11 =
      ((80685881368527806198379666664098436 * 10 ^ 70 +
        4035342240146572400039066192550872076874122392851860523204138304134368) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 12 = 0 +
    12 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 12 = 12 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5B2A3_coeff_12 :
    recurrence5B2A3.coeff 12 =
      -((39451015449839027205434463431274840070 * 10 ^ 70 +
        9716122410057859279776305579854381767096470892876480623890894011579938) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 13 = 0 +
    13 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5B2A3_coeff_13 :
    recurrence5B2A3.coeff 13 =
      ((14928661738902549544953094388387568468356 * 10 ^ 70 +
        6883653049926644637895520442782877172236196493175077762171229582860746) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 14 = 0 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5B2A3_coeff_14 :
    recurrence5B2A3.coeff 14 =
      -((3309403744765495708861557942693146273670796 * 10 ^ 70 +
        6159674101069059350255221427915467761206445076674940799391699649547868) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 15 = 0 +
    15 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5B2A3_coeff_15 :
    recurrence5B2A3.coeff 15 =
      -((266695074734179130285414578358011786241585914 * 10 ^ 70 +
        3016397300599063812413042928649543960497272379335839931554174882005458) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 16 = 0 +
    16 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 16 = 16 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5B2A3_coeff_16 :
    recurrence5B2A3.coeff 16 =
      ((614321358346969485824895242220557397272142477977 * 10 ^ 70 +
        8005604558773250322518125040849402463385742447285856402823528131632022) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 17 = 0 +
    17 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5B2A3_coeff_17 :
    recurrence5B2A3.coeff 17 =
      -((314195368404515848429471610891023753735826610461419 * 10 ^ 70 +
        9545312049223349189380267403576368536128157336408271952541323952780613) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 18 = 0 +
    18 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5B2A3_coeff_18 :
    recurrence5B2A3.coeff 18 =
      ((106506029613026494257547251918647662232821638580092036 * 10 ^ 70 +
        6249968828713541226410404890527487393867124939936817945309672634442711) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 19 = 0 +
    19 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5B2A3_coeff_19 :
    recurrence5B2A3.coeff 19 =
      -((27576801060988620893449676378842836398442859240049319111 * 10 ^ 70 +
        9537037430399395302203761281193735904134672219966051812408990373029620) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 20 = 0 +
    20 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 20 = 20 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5B2A3_coeff_20 :
    recurrence5B2A3.coeff 20 =
      ((5733673844866061884909006543586937915191309921274851564495 * 10 ^ 70 +
        4782054071966450144608348651265565145354699350858644712598536501537893) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 21 = 0 +
    21 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5B2A3_coeff_21 :
    recurrence5B2A3.coeff 21 =
      -((977846365858285975221416536576756484776026272810307715609494 * 10 ^ 70 +
        8660276690617959881947629708490276277159967019919713912792564598833164) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 22 = 0 +
    22 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 22 = 22 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5B2A3_coeff_22 :
    recurrence5B2A3.coeff 22 =
      ((137494637628474005371814005519534384935147387296005538996058131 * 10 ^ 70 +
        7052803242039680305481700322557314369312626428283188402750142596183152) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 23 = 0 +
    23 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5B2A3_coeff_23 :
    recurrence5B2A3.coeff 23 =
      -((15747755687208637018898151969676198149313028231363457459772032261 * 10 ^ 70 +
        5487312527009765632789786906563643387408520972128431728434194258202157) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 24 = 0 +
    24 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 24 = 24 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5B2A3_coeff_24 :
    recurrence5B2A3.coeff 24 =
      ((1401178869028824310350100435205873648993531564273839038022093943923 * 10 ^ 70 +
        3541897079684633738253899887100236752343235751112489595315618572144411) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 25 = 0 +
    25 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5B2A3_coeff_25 :
    recurrence5B2A3.coeff 25 =
      -((80729945864207073787862589620022060395237496757766482683100071898472 * 10 ^ 70 +
        4649883337031204430003582772259833642453701715590087657623122081172992) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 26 = 0 +
    26 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 26 = 26 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5B2A3_coeff_26 :
    recurrence5B2A3.coeff 26 =
      -((685458418254170251958521924275991205798431261390594952311324579081041 * 10 ^ 70 +
        1691281887654079901195401585657374861373126982618037563739558595611640) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 27 = 0 +
    27 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5B2A3_coeff_27 :
    recurrence5B2A3.coeff 27 =
      (((95 * 10 ^ 70 +
        8488228708065530801037730098272777929732297956450098628946213172755678) * 10 ^ 70 +
        6137250320034446471363334633000678755560390888189021223461995665786840) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 28 = 0 +
    28 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 28 = 28 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5B2A3_coeff_28 :
    recurrence5B2A3.coeff 28 =
      -(((15990 * 10 ^ 70 +
        6825088928112687924426873402986047602908679404585280166732921870978978) * 10 ^ 70 +
        2471067628452081328691830070051009703148434022590746299712608290818484) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 29 = 0 +
    29 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 29 = 29 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5B2A3_coeff_29 :
    recurrence5B2A3.coeff 29 =
      (((1852412 * 10 ^ 70 +
        2861996398566083586988660263927469798467847644888293196268483499119348) * 10 ^ 70 +
        1032265307118300882353272527781912502564709714134529180428925798997121) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 30 = 0 +
    30 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 30 = 30 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5B2A3_coeff_30 :
    recurrence5B2A3.coeff 30 =
      -(((174239510 * 10 ^ 70 +
        6082551417134484622361297411955512406130827696915755165605975060380952) * 10 ^ 70 +
        5672346138066992343828162825800217494855269315020561919096771992576336) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 31 = 0 +
    31 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 31 = 31 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5B2A3_coeff_31 :
    recurrence5B2A3.coeff 31 =
      (((14031464953 * 10 ^ 70 +
        1371245153516668858050581109262726413370630177747171405326594451952540) * 10 ^ 70 +
        3179714221935118406948300425105974761774480957645390600933449413556265) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 32 = 0 +
    32 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5B2A3_coeff_32 :
    recurrence5B2A3.coeff 32 =
      -(((992335319001 * 10 ^ 70 +
        8034000792929107285560952625546017467406435450018877249397301258712263) * 10 ^ 70 +
        2732032477133213195827142044127925392938597514376098677518357764790835) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_33 :
    recurrence5B2A3.coeff 33 =
      (((62549458729087 * 10 ^ 70 +
        1341834616221783659696873183821881871002631283248008551874216703446149) * 10 ^ 70 +
        6078265450893506898386312138058882500762472207318270839288670659636752) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_34 :
    recurrence5B2A3.coeff 34 =
      -(((3548035645242998 * 10 ^ 70 +
        0918756622190932849900342816491146675011589890318335143740921567656608) * 10 ^ 70 +
        2008323112620156526600141886854791940256828111055310088504440802322774) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_35 :
    recurrence5B2A3.coeff 35 =
      (((182354433301505809 * 10 ^ 70 +
        8361264038364665053283495101902422265222331281768094944841524017260876) * 10 ^ 70 +
        7860932136983837819591171270710689912661797047802208232211379750866404) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_36 :
    recurrence5B2A3.coeff 36 =
      -(((8535306833022723299 * 10 ^ 70 +
        2071568849653384531445940704057075889375642826967242745267730508134387) * 10 ^ 70 +
        8715323126132868459715488936067555393515162340271124715720633152097752) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_37 :
    recurrence5B2A3.coeff 37 =
      (((365255099519345970312 * 10 ^ 70 +
        7358596547880051862428906072201735347219998874546416393621948287548680) * 10 ^ 70 +
        9318568870140124317498248759887091251163121033935787891470575782795204) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_38 :
    recurrence5B2A3.coeff 38 =
      -(((14334032742164091542144 * 10 ^ 70 +
        4120349591932577704460624462199253620040739167549806102302161563242622) * 10 ^ 70 +
        6975887052580517908442921147661138450482263156261695151825822206413498) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_39 :
    recurrence5B2A3.coeff 39 =
      (((517065464045379550986105 * 10 ^ 70 +
        6684587621405328717152069896036235592423471429319941281872281283161428) * 10 ^ 70 +
        5069132238244959650613293690277366727789207838312949259949623628592552) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_40 :
    recurrence5B2A3.coeff 40 =
      -(((17173341875379752338804592 * 10 ^ 70 +
        3698070101467443981991421970372005984626735159405502606600253275098393) * 10 ^ 70 +
        1454039409014537010463771320244836488039302322442573210096628938009274) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_41 :
    recurrence5B2A3.coeff 41 =
      (((525695150154541178255630283 * 10 ^ 70 +
        0149316001594625651076226193978683228352908107846271146200375403566744) * 10 ^ 70 +
        1335343364649975590903557807723120677133160518549046327739570838936971) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_42 :
    recurrence5B2A3.coeff 42 =
      -(((14835008875467158119154052960 * 10 ^ 70 +
        6269401344698947142370537162325283395605522054117850659654959199634540) * 10 ^ 70 +
        7948588724912483994591438538993048391272673175301003230139551409601109) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_43 :
    recurrence5B2A3.coeff 43 =
      (((385649129273905323389381450642 * 10 ^ 70 +
        4473483388104538775292049997248487501656860719491117442468406486743947) * 10 ^ 70 +
        5078607917633829227617529128841548871455053053784317098410617695418697) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_44 :
    recurrence5B2A3.coeff 44 =
      -(((9215309380317180359133175785134 * 10 ^ 70 +
        6074491273945046458528082566385906208131835283767867028468342766023483) * 10 ^ 70 +
        2189987588228722994109628860189127712660304019496891398520392203047379) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_45 :
    recurrence5B2A3.coeff 45 =
      (((201525843956888587323508889382934 * 10 ^ 70 +
        5474630331849431171751170260993451682017819490527492664233072453887897) * 10 ^ 70 +
        6650090690301966940478011625634393132055881218421783015330315642498923) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_46 :
    recurrence5B2A3.coeff 46 =
      -(((3999740709430731059029178198875610 * 10 ^ 70 +
        4687083221896339147690070660719371567390938053630678880590326470012882) * 10 ^ 70 +
        6970225624712572489024964612312155634204490399722764316296261667179150) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_47 :
    recurrence5B2A3.coeff 47 =
      (((70885694384935330865497597691632143 * 10 ^ 70 +
        2572129957067957361302052552132758270643187701393043414238804818838895) * 10 ^ 70 +
        2502732739432198044862604498142151297041743628370798730610459891516291) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_48 :
    recurrence5B2A3.coeff 48 =
      -(((1083057228487426266443873357908744511 * 10 ^ 70 +
        0718229689710025696909028301209172306237384715658597587739790636674132) * 10 ^ 70 +
        5679620637431603655388521990725582753618477268230525519261462839994232) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_49 :
    recurrence5B2A3.coeff 49 =
      (((12964182321997468363937438153776636331 * 10 ^ 70 +
        7739128326263658601830694239071580926316688470265687877458239712675095) * 10 ^ 70 +
        0507034097716412651021015015102007123413511746388080994091774026209530) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_50 :
    recurrence5B2A3.coeff 50 =
      -(((74571863411455054022223223782457420399 * 10 ^ 70 +
        1572634333139691897231476638866805312254533050745637054348835568870610) * 10 ^ 70 +
        0133859325995471086903139631392436530917873422713666536851786990599427) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_51 :
    recurrence5B2A3.coeff 51 =
      -(((1826279520946449755173278280292918037013 * 10 ^ 70 +
        4411419700413374271156048249476942165040889130820821193235661746313950) * 10 ^ 70 +
        9474771503535711425443127307831783767995182312526957074643519778896253) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_52 :
    recurrence5B2A3.coeff 52 =
      (((86418051567073191523246692440193689781506 * 10 ^ 70 +
        1578440760912598640819801289858167816029779632145206363468191828195034) * 10 ^ 70 +
        6547400551780831899670822190088427643140458553114840533165951086030849) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_53 :
    recurrence5B2A3.coeff 53 =
      -(((2312166781136500856358267741739788030149586 * 10 ^ 70 +
        7779486647642006996555093639603342568471722961487010583173931608991073) * 10 ^ 70 +
        9943392267667976899499772312596449179116698716646849931753528099961664) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_54 :
    recurrence5B2A3.coeff 54 =
      (((49872035807140515177544230343538163717710793 * 10 ^ 70 +
        8421683544147173807643607111732609730047903306423411189486482123951776) * 10 ^ 70 +
        4282733730730463739923806252551195782471463358156710799960123116232385) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_55 :
    recurrence5B2A3.coeff 55 =
      -(((942435953353534231086156762173287137607151128 * 10 ^ 70 +
        4868248946724115503912894862025446614676845528610074159959416999983035) * 10 ^ 70 +
        3290268126503778303481393203067129038612638684002158728862214788521380) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_56 :
    recurrence5B2A3.coeff 56 =
      (((16135651167445760787874831692758562324092926064 * 10 ^ 70 +
        6411229352820321030411883293293137050405452100600401807261433771046154) * 10 ^ 70 +
        6077280770288101990490757551568023349970197802399078124541066874732487) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_57 :
    recurrence5B2A3.coeff 57 =
      -(((254655380693056466298575389299573363085455791765 * 10 ^ 70 +
        6361140825818979334081435409191081751507521015059499595994906992476558) * 10 ^ 70 +
        1776418334357286977717575456342794170066240023556798388559923534588347) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_58 :
    recurrence5B2A3.coeff 58 =
      (((3742859011871154074604584766049186399285060705806 * 10 ^ 70 +
        8595569232338882052251963125704264794897035198079463137860059382638700) * 10 ^ 70 +
        7405685174267022020549552923907709955766393004907603809301090640587350) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_59 :
    recurrence5B2A3.coeff 59 =
      -(((51577909419328353931637335291841978755308123861753 * 10 ^ 70 +
        8560480892925055943327869042831289328425418057437755329179739332156279) * 10 ^ 70 +
        3026666901422395693332784849517596979761457155707853350233005931814902) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_60 :
    recurrence5B2A3.coeff 60 =
      (((669581922927763510539511648393454717366854141792100 * 10 ^ 70 +
        6613890652061859599651440488446021297363200398949160687236489830425848) * 10 ^ 70 +
        9229790378204767218950835868460360183808996175893309840146084732535578) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_61 :
    recurrence5B2A3.coeff 61 =
      -(((8218158921459420475367716338225249460983131096824068 * 10 ^ 70 +
        3576643203806436971539790558677782799339301980013598243007352535729119) * 10 ^ 70 +
        7848226924121081740367649062992989268471819062835206385358528981504802) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_62 :
    recurrence5B2A3.coeff 62 =
      (((95629589049018379852875611769524403946154274417105407 * 10 ^ 70 +
        6389098692724101306007976632597971937585853463418929243917423695146460) * 10 ^ 70 +
        0284156988018670019718181681419881217526652791326172546526296429092050) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_63 :
    recurrence5B2A3.coeff 63 =
      -(((1057415677724149559990071593310204482985466041363540000 * 10 ^ 70 +
        3813898039713585130224462939021765073966091072710528211695854637379585) * 10 ^ 70 +
        2057338180623653147955373006183954519373150474926784057754908159722503) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_64 :
    recurrence5B2A3.coeff 64 =
      (((11131734337061046244281591750857855137858474774782706155 * 10 ^ 70 +
        9697793843522348909802288095765188325104281785466840465852660209523126) * 10 ^ 70 +
        3176955364013101293712830231273900411679951246013163720366414240099824) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_65 :
    recurrence5B2A3.coeff 65 =
      -(((111751565360563411407318149986742080020952401624125830436 * 10 ^ 70 +
        6380688002683559201141080373077972316571917141387880463171426761350791) * 10 ^ 70 +
        6018801865618316169963265855028523372089080124996070806322307167887976) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_66 :
    recurrence5B2A3.coeff 66 =
      (((1071369020372226127107266097435160385187556350330011149112 * 10 ^ 70 +
        7648565067747328953725959135564162481608917483057254949073694698299270) * 10 ^ 70 +
        2852465176834899376099101167180102380211895700218596042852727588772103) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_67 :
    recurrence5B2A3.coeff 67 =
      -(((9821347808115563604478379294804228360554006520019848703959 * 10 ^ 70 +
        9066552680274278321409025285189137696812222946137600482582319027850464) * 10 ^ 70 +
        8033829487626532016389579342823453770202652693205570143812173446796321) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_68 :
    recurrence5B2A3.coeff 68 =
      (((86187942791056712528943664285048413792797863315912710673708 * 10 ^ 70 +
        5428946713201534033508221621917554126998021371381152890119423264655152) * 10 ^ 70 +
        3048495261081767307130521514253367641482647873070360148543455870713303) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_69 :
    recurrence5B2A3.coeff 69 =
      -(((724798989003673749815631843132870524112656855758406275650795 * 10 ^ 70 +
        0003809410770509986871118552488100890512532370997159058612753792636516) * 10 ^ 70 +
        2972641387363191958028552870159786853226811560839164756097744868499262) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_70 :
    recurrence5B2A3.coeff 70 =
      (((5846548106794065843859610878115204129103614721729198227863848 * 10 ^ 70 +
        9196463342247210029244737040210005954739129324972809936273164802474726) * 10 ^ 70 +
        7357941188257369952113622150129761580696343655394950159521745830228341) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_71 :
    recurrence5B2A3.coeff 71 =
      -(((45276874517566439959353772420185342179460340419085055500131648 * 10 ^ 70 +
        8936880353301685318808570710962552060851501598651454218844193877290202) * 10 ^ 70 +
        3171288545247902542508102456778745788464218299662088539819561663218876) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_72 :
    recurrence5B2A3.coeff 72 =
      (((336903646885820320164661171112401015056728574502945368936666788 * 10 ^ 70 +
        9881539970493366196374452980033323852665771203249574090456698990542814) * 10 ^ 70 +
        3792953983950514804797215617977138082373352854328039417912056833970681) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_73 :
    recurrence5B2A3.coeff 73 =
      -(((2410580101900732468459372028230355345011916719177100966566554644 * 10 ^ 70 +
        1943824822035791102735412525035222268515748367816959837930432250761343) * 10 ^ 70 +
        4922148949013835977297474632536285369727002157117423649415089979411276) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_74 :
    recurrence5B2A3.coeff 74 =
      (((16597315064353635090714153365577401957607502167817364370396479865 * 10 ^ 70 +
        8171145065651527744029872492217927316879021923558001131315185912016309) * 10 ^ 70 +
        7250910307485037632131729420121214145759025170637290710853172348933478) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_75 :
    recurrence5B2A3.coeff 75 =
      -(((110039905017029298760169837877016084954566607247911876523631498787 * 10 ^ 70 +
        9417518995913380914891061885278986793300525512166024964914032781329958) * 10 ^ 70 +
        6456408848478379587280987005219004871491329211426091172887808651917760) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_76 :
    recurrence5B2A3.coeff 76 =
      (((702972000350013245955322613656681420735011716450894800331637068530 * 10 ^ 70 +
        9932459131440250609378848032172728009529158280781031318529397197678776) * 10 ^ 70 +
        6458615145672827241722160659682479245236959827493521224031724704885098) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_77 :
    recurrence5B2A3.coeff 77 =
      -(((4329779958212120427889606388769590092936593210974822576118738434559 * 10 ^ 70 +
        9787853504913941047312639499886234495949304497384704722572927371021082) * 10 ^ 70 +
        4023814944821354307048650852022256576623537249432971103321108063154259) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_78 :
    recurrence5B2A3.coeff 78 =
      (((25726727755711259928615227948949933269408442596649380201635480580418 * 10 ^ 70 +
        3653182869829306341642238145845677137182405389995478589999462396073073) * 10 ^ 70 +
        5455477974337891154805287620159983047761725058737732054422594757248919) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_79 :
    recurrence5B2A3.coeff 79 =
      -(((147547760890893234742435146994880816785167307189907949526463673641212 * 10 ^ 70 +
        8061761067467296030504665484533220323287969878374286371995019838914557) * 10 ^ 70 +
        2080461817471445660501560081726485878649441986355318724352096276902349) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_80 :
    recurrence5B2A3.coeff 80 =
      (((817215944845918193657488262389390617869336757206739980985387424743273 * 10 ^ 70 +
        7546364863870498169625126528642392797366970325825961500870668556200647) * 10 ^ 70 +
        5346101428303010693758358319081541116930518183465594404120427817939135) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_81 :
    recurrence5B2A3.coeff 81 =
      -(((4373338563714742736814613338819085156716484555195427998190817761868559 * 10 ^ 70 +
        8104815553645428688311378913125416519839956992315012306353862573254423) * 10 ^ 70 +
        4296558449170826347164408997946986199597732291633439264752195475682984) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_82 :
    recurrence5B2A3.coeff 82 =
      ((((2 * 10 ^ 70 +
        2623883406746940439340840572603864290402844542982386231531447294142522) * 10 ^ 70 +
        3092983837364800427354164866343468825792978895589724606573174856514150) * 10 ^ 70 +
        5220550882845309025087734555257808950824646320059541234767589872823220) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_83 :
    recurrence5B2A3.coeff 83 =
      -((((11 * 10 ^ 70 +
        3186624618196334420906577025225258832269357545844569867965444142588878) * 10 ^ 70 +
        7545366920438403989972896497892276989025539564554349368361095821258775) * 10 ^ 70 +
        5942868168755347703207396778912200031554944390606235431151957854175558) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_84 :
    recurrence5B2A3.coeff 84 =
      ((((54 * 10 ^ 70 +
        7878156494365697027448067278377545768932741217649356114883794378412025) * 10 ^ 70 +
        3084057951068641410520469700013033624286311982876949446800855259241597) * 10 ^ 70 +
        3998103025216453126052855011366259168168999081961075133816830154644924) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_85 :
    recurrence5B2A3.coeff 85 =
      -((((256 * 10 ^ 70 +
        6919077106080389866352183940601721734765972719363204614538191614828675) * 10 ^ 70 +
        2687996558672308518592732978820580994227314694727126698782699732691765) * 10 ^ 70 +
        1920355347940502908682551984781736655560774398156265231057041044227526) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_86 :
    recurrence5B2A3.coeff 86 =
      ((((1164 * 10 ^ 70 +
        5278220519829598706850552953889792056460986687710167201313997495226117) * 10 ^ 70 +
        7374874589053830423827364651764415583570513980120837567619587593336612) * 10 ^ 70 +
        6093720390495998310676239614077308499740642598070304241770669392890996) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_87 :
    recurrence5B2A3.coeff 87 =
      -((((5117 * 10 ^ 70 +
        5184692064330121124286989025675350827219073033233590556166041746391011) * 10 ^ 70 +
        9390007711565398655142269372062963456399485379610884333637258002697273) * 10 ^ 70 +
        7726333596008580609954263681970259685335205151995914345159495075419744) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_88 :
    recurrence5B2A3.coeff 88 =
      ((((21791 * 10 ^ 70 +
        9309493578712100060066970941930016257067878139393011226925984118057689) * 10 ^ 70 +
        0984077696321930910924457030405365103989725310985183551522406545077882) * 10 ^ 70 +
        9954681866770284743434867480234639331535968826741665489764103162493348) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_89 :
    recurrence5B2A3.coeff 89 =
      -((((89951 * 10 ^ 70 +
        1037363802898470632877984446817157451949325683362273871896103013010870) * 10 ^ 70 +
        6102351380315471094345985671449937553881047783966390476590555646224298) * 10 ^ 70 +
        2799502937560587329297544047019241475761042920249569935804969561537507) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_90 :
    recurrence5B2A3.coeff 90 =
      ((((360025 * 10 ^ 70 +
        0076308229966577967727084300347156200538323255271737240329256512299766) * 10 ^ 70 +
        5351395852986492513968200691007011550260053404339527607789375952106933) * 10 ^ 70 +
        9044553005299816411199959812618532774650591171562361877455722989286318) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_91 :
    recurrence5B2A3.coeff 91 =
      -((((1397682 * 10 ^ 70 +
        6615133942047095067324351216043666631053012657932354222613358060802545) * 10 ^ 70 +
        4384263800798444082525470334635939374574297288306732374577815164416198) * 10 ^ 70 +
        3339984504161438590865840830784176910840261148068382357948219708105521) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_92 :
    recurrence5B2A3.coeff 92 =
      ((((5264562 * 10 ^ 70 +
        5652547880764799433907888166798889864853615785361298482096252392549464) * 10 ^ 70 +
        0862410181870916162248436065648683111088123893666597623238849197440441) * 10 ^ 70 +
        5864066211801099415869096027169362249864631774492666602064654799116777) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_93 :
    recurrence5B2A3.coeff 93 =
      -((((19244908 * 10 ^ 70 +
        4154160584872861416181911131679471762375752911624663370818058546968468) * 10 ^ 70 +
        5484255621102801677453702022030332114213331041957554794631006795697179) * 10 ^ 70 +
        2850115144350096020138672814392955349950454258444044809268816879529416) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_94 :
    recurrence5B2A3.coeff 94 =
      ((((68294464 * 10 ^ 70 +
        6832231365409808962415865481866616836789509485715267663461569312947171) * 10 ^ 70 +
        6426684691296030042729833569314148936608543353081295492026054955536381) * 10 ^ 70 +
        4565657931014872235954683841978354188878725510320861802319738056151133) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_95 :
    recurrence5B2A3.coeff 95 =
      -((((235332529 * 10 ^ 70 +
        1321902849744385016547923059632562672753266315327796883925913680582285) * 10 ^ 70 +
        5331626638896457775385776527178463105819621065781024388822321373428515) * 10 ^ 70 +
        6567145740607056805901616472264910321108142233114376531356313882535379) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_96 :
    recurrence5B2A3.coeff 96 =
      ((((787608845 * 10 ^ 70 +
        3416746072208128282504193226296369454038430053072735037117765169186639) * 10 ^ 70 +
        7468581661059142647577316808695002282174744549903141286032257490660240) * 10 ^ 70 +
        6777418963253092056123990547761990903624085735081196368475874216573487) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_97 :
    recurrence5B2A3.coeff 97 =
      -((((2560776105 * 10 ^ 70 +
        8357667339565371445888825889772606606518717870847931942674953805806347) * 10 ^ 70 +
        0432373685179909525959009392353063692451405076552730336131302343609724) * 10 ^ 70 +
        3884218305933510582573003187838881612639545711432549197857599888973485) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_98 :
    recurrence5B2A3.coeff 98 =
      ((((8090220058 * 10 ^ 70 +
        6485326091819152470802617141505501199708583085865492778488112738079450) * 10 ^ 70 +
        0405388348239093484470919576211471502253837754416306014467733533296055) * 10 ^ 70 +
        1882739065996701547412725426773778807222404583407648549949761276180124) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_99 :
    recurrence5B2A3.coeff 99 =
      -((((24840899173 * 10 ^ 70 +
        8804501288598811737119163495811858340375988502001528128309282121112283) * 10 ^ 70 +
        0737639581166414561278828910360304903983062001628649166012535067440774) * 10 ^ 70 +
        3170500886786883612967368276037189068203566122192018577842187809350730) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_100 :
    recurrence5B2A3.coeff 100 =
      ((((74144426336 * 10 ^ 70 +
        9542790669645276888839702514968883013814001441798965574187861502244227) * 10 ^ 70 +
        1381930673667927841478658882852202394741300860572594699525664808726416) * 10 ^ 70 +
        8984719140319975893482498703545017562091556229332889152260261483827795) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_101 :
    recurrence5B2A3.coeff 101 =
      -((((215166905515 * 10 ^ 70 +
        4205446799119323305113810269756852992812099766758597898133620826746748) * 10 ^ 70 +
        3689185590484108651347306695116095848075188416221806841422078729576165) * 10 ^ 70 +
        8699188114599461095147452017961146184534840156503052524551354490302372) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_102 :
    recurrence5B2A3.coeff 102 =
      ((((607205194546 * 10 ^ 70 +
        6865255698568965348883493612918064390862346154255908481266306903824430) * 10 ^ 70 +
        4868541066290895841644215071609100623004861440640267165918044808048869) * 10 ^ 70 +
        4376000684796166256421928582142978976559844231584584790309277187166839) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_103 :
    recurrence5B2A3.coeff 103 =
      -((((1666601055115 * 10 ^ 70 +
        8413331559457622201112132478683403272767374785470242877772826352442336) * 10 ^ 70 +
        7794813071766641831225393244066999409836468580184452020789108110503676) * 10 ^ 70 +
        9124507364487486341154686725867566568527796152335095424581690083890493) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_104 :
    recurrence5B2A3.coeff 104 =
      ((((4449724311707 * 10 ^ 70 +
        5528475110741929771225498177392710750198967783487820138762141316999521) * 10 ^ 70 +
        0586617557991161649409731722372756609823326861555908025470721555663362) * 10 ^ 70 +
        6620613079233469769868901078983760565109370333474683332099623407588667) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_105 :
    recurrence5B2A3.coeff 105 =
      -((((11558594426967 * 10 ^ 70 +
        4242270752250713846996585908611530389293540357923315253783761302681736) * 10 ^ 70 +
        9016115678204476096210988340519611754258678531148753341828090118010883) * 10 ^ 70 +
        8144124294851275403241579097955775934347159120562708408406288504849914) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_106 :
    recurrence5B2A3.coeff 106 =
      ((((29215194258663 * 10 ^ 70 +
        1858518730585043090078269468634577134833953400636216342959530394308869) * 10 ^ 70 +
        3974771638818023577014688902311335412377282545198734206146032560407806) * 10 ^ 70 +
        3783304414084001480339154538569467395834027932908281245814180889223223) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_107 :
    recurrence5B2A3.coeff 107 =
      -((((71862442653960 * 10 ^ 70 +
        4327944933886316289821605164655064023874241289222124694583255599082150) * 10 ^ 70 +
        6817747728519014344068870660370977289279458558592055851378534107110299) * 10 ^ 70 +
        6042743992005088168556356295136161020573388988842024865355387643726382) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_108 :
    recurrence5B2A3.coeff 108 =
      ((((172043604149330 * 10 ^ 70 +
        8662575596403648884814847175897615922604057194708352991141983563584774) * 10 ^ 70 +
        9699998341041084183627836750940032052340027464690281121971226377419190) * 10 ^ 70 +
        4245783808899922997468100106343312932631883363525973120063612003510689) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_109 :
    recurrence5B2A3.coeff 109 =
      -((((400930145380199 * 10 ^ 70 +
        7404224884403209166198925590563064128154340858751880196926742814068342) * 10 ^ 70 +
        7157199657785047915283629869982986271008835637363821088676231603858172) * 10 ^ 70 +
        6307084736021533939971111282235596041384304914705741710911764917910183) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_110 :
    recurrence5B2A3.coeff 110 =
      ((((909576314579630 * 10 ^ 70 +
        9160574727787648411618796462680937681556430178204139103510442560076812) * 10 ^ 70 +
        2150341729126651593978334529271839198715060456165480756036388675189697) * 10 ^ 70 +
        9304191814582577209939417096902817200209478062167430273599208633727074) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_111 :
    recurrence5B2A3.coeff 111 =
      -((((2009059614153493 * 10 ^ 70 +
        4470269982902990488831644752763395340736084849704989224511128282321548) * 10 ^ 70 +
        3867696388637757105245562479326342376882653668807775875196512538024126) * 10 ^ 70 +
        1833748677417134273480861918902963694000067337675067589126190815006254) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_112 :
    recurrence5B2A3.coeff 112 =
      ((((4320849099820376 * 10 ^ 70 +
        4375271610202831943136738185269683734305866248996144067081854373161933) * 10 ^ 70 +
        4115899751374483892359717310013326605049299949861600725510377298389463) * 10 ^ 70 +
        3334988102235761427018211384663128343145700862360560269589192427887973) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_113 :
    recurrence5B2A3.coeff 113 =
      -((((9049063142307157 * 10 ^ 70 +
        6303646147806005100305618741447193685357596755787361551761143789766766) * 10 ^ 70 +
        6097810548505522986043922019921955112162202127495744251311078058917457) * 10 ^ 70 +
        2355907576699962856706329704096613456267496299590952189226815329593192) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_114 :
    recurrence5B2A3.coeff 114 =
      ((((18455603958161796 * 10 ^ 70 +
        9288314176859454495495379034151244047779375874620741943550603683162958) * 10 ^ 70 +
        6350923420518450847849646564999308021742622962148994439374611734953312) * 10 ^ 70 +
        6258104827782047691090813289857365146686838669169993229860273878220412) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_115 :
    recurrence5B2A3.coeff 115 =
      -((((36658192033583127 * 10 ^ 70 +
        7010259407599952079541301510418114147224278673248812203414656859537238) * 10 ^ 70 +
        6742903313546133081912669864558407817440535630699701042326191983866225) * 10 ^ 70 +
        3660168922041714506165186766269602072591909338748671020279086924067519) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_116 :
    recurrence5B2A3.coeff 116 =
      ((((70917916640303904 * 10 ^ 70 +
        5973069713843251999738561619924243631033684848152016537886557996310194) * 10 ^ 70 +
        1664055667798332085687691643963857751541231265542110673130476298648055) * 10 ^ 70 +
        4345902163931158531636408011069762451190938921630458252125205219468937) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_117 :
    recurrence5B2A3.coeff 117 =
      -((((133629664983187681 * 10 ^ 70 +
        2168952335213316681713979152288917123921069565546588280532807794483858) * 10 ^ 70 +
        9953148050894223583046615601069740059414931423024869762442697928885857) * 10 ^ 70 +
        0489595897074737984345486578415302135683255523565406642355885319744892) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_118 :
    recurrence5B2A3.coeff 118 =
      ((((245260281575892067 * 10 ^ 70 +
        1364592537800862021210958466730135087181339964009923061243809184203117) * 10 ^ 70 +
        5264141402137875991982841493697543941540607241966598005047012584292152) * 10 ^ 70 +
        6543686552662006862262840869467790041890330917881962300670324257233839) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_119 :
    recurrence5B2A3.coeff 119 =
      -((((438469905722136426 * 10 ^ 70 +
        2318824776481878422568142042362846191557577173126159738179377212796500) * 10 ^ 70 +
        2230383792161630239792751292018457406286341733897972815793842660653944) * 10 ^ 70 +
        4266533862912035205161763820174812634881286904933618150822626146061999) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_120 :
    recurrence5B2A3.coeff 120 =
      ((((763565676212080287 * 10 ^ 70 +
        6068766178062904465361614677170918497542620678950572223120987037568209) * 10 ^ 70 +
        4216321797487496093797259976659157138035160123733149965926921269965272) * 10 ^ 70 +
        2664919039347546110135417982085134441550014734042486474413243597588550) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_121 :
    recurrence5B2A3.coeff 121 =
      -((((1295231736608374687 * 10 ^ 70 +
        3243338841888421005106527935174686005550380781911726156807413225594270) * 10 ^ 70 +
        7533442520543882487792905479825821433177642148296484829846620863417544) * 10 ^ 70 +
        6777808875285760354857082658366503135414113836396891274931597625502799) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_122 :
    recurrence5B2A3.coeff 122 =
      ((((2140117422592551600 * 10 ^ 70 +
        8120256459904712878157472894784190337815653108323566925596125234318412) * 10 ^ 70 +
        1625589790050064207134938244347272019044497118365000887214120800341662) * 10 ^ 70 +
        9094216001183664277958828786351603867186793282191686552638266159235779) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_123 :
    recurrence5B2A3.coeff 123 =
      -((((3444331139601073357 * 10 ^ 70 +
        6249834642942566167277208703379837359330371717411727044872314681913349) * 10 ^ 70 +
        3300985321203221493634282054648045976640554241196917673414468910522680) * 10 ^ 70 +
        2342649400860228995593115348700239894152662640086865384463742452479683) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_124 :
    recurrence5B2A3.coeff 124 =
      ((((5399211290671903506 * 10 ^ 70 +
        7720517915564606831139632924536612564949870249158780247771527891225560) * 10 ^ 70 +
        7227034459837886503885674323682225735018933153049115157373336837399780) * 10 ^ 70 +
        1397405583690804302759950723458561269201461317962099706010610460370171) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_125 :
    recurrence5B2A3.coeff 125 =
      -((((8243028450965862631 * 10 ^ 70 +
        9839476722543758071849892275251241729204251200993336720448097022316139) * 10 ^ 70 +
        3916423780254615213907658171186470012492526757878634627856024828653923) * 10 ^ 70 +
        8373022291896108183819157596268071406827482194305975918103215773575397) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_126 :
    recurrence5B2A3.coeff 126 =
      ((((12255700288715669650 * 10 ^ 70 +
        1964708036935284647061234295522558295535914244113183011538090900172592) * 10 ^ 70 +
        7499509416029674484514425248928654848693806102501205645752037237251381) * 10 ^ 70 +
        5647251338895833522060556562022542399689688269972636252414955547193160) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_127 :
    recurrence5B2A3.coeff 127 =
      -((((17743434577662230447 * 10 ^ 70 +
        8029165453221227216165350640762365598112183584398451618999978819496261) * 10 ^ 70 +
        9197904004784743199018233574138225591084350124353970291972425296205603) * 10 ^ 70 +
        0049160894336251348053157468443747360048576583567301721065182170698724) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_128 :
    recurrence5B2A3.coeff 128 =
      ((((25010751917534496069 * 10 ^ 70 +
        4503612032519278076884775265219909535223028224336105062504649110718003) * 10 ^ 70 +
        3981704783706628942379909237175087647775411347811215339369722004980183) * 10 ^ 70 +
        8247313827720284444327859997331643422339680499886617677080019950430142) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_129 :
    recurrence5B2A3.coeff 129 =
      -((((34318825982852141717 * 10 ^ 70 +
        9334232549110111392165262340953899932713623607717746009770546454987776) * 10 ^ 70 +
        5582105572149614544978511421769050103532103001512455901007061845045351) * 10 ^ 70 +
        6399101001924239303151833768950434098735185839706472128077238014013951) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_130 :
    recurrence5B2A3.coeff 130 =
      ((((45831602132395917870 * 10 ^ 70 +
        7829192978373508557453961569901201944939536149953529085553373054870586) * 10 ^ 70 +
        7708135639456582875565206966784388842850140245623912648325437322865331) * 10 ^ 70 +
        1584138504037191536607155760192096328353124929460449546577340276275369) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_131 :
    recurrence5B2A3.coeff 131 =
      -((((59554526543346166542 * 10 ^ 70 +
        9303112360929498959593294232547239821117214842259070175047378058771645) * 10 ^ 70 +
        5022870868411257925633764699374034335228354900442693407325341506706156) * 10 ^ 70 +
        2910184186985120289697555567874873885521952207340540229746499539571652) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_132 :
    recurrence5B2A3.coeff 132 =
      ((((75274400258592479230 * 10 ^ 70 +
        1516198244119880635305090726100458830343153240082927224965732751779741) * 10 ^ 70 +
        7337079127514056412433271536206799955167529425615198719443704443948827) * 10 ^ 70 +
        2151170766267983728737543961869807765529281617182953295825883860491351) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_133 :
    recurrence5B2A3.coeff 133 =
      -((((92511995630238847861 * 10 ^ 70 +
        4672348440093901149264222817894880502373773610750194493410400592996173) * 10 ^ 70 +
        6506249662686864612768389645804425967891634526457033541598635559471999) * 10 ^ 70 +
        1728993815237876886989787324825847955980522636040114745452609468154802) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_134 :
    recurrence5B2A3.coeff 134 =
      ((((110500575228319956720 * 10 ^ 70 +
        4910864670853958349879333742294653112311849736613949843059066317091391) * 10 ^ 70 +
        3892817555082958469184209744073936246223134456501273146801250799325134) * 10 ^ 70 +
        5442322160252902334102084014936888047766330044059090839944638983593495) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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

theorem recurrence5B2A3_coeff_135 :
    recurrence5B2A3.coeff 135 =
      -((((128202348554159666327 * 10 ^ 70 +
        3979965174399990346030099541410726176784661362875526650927636848649102) * 10 ^ 70 +
        3146892706628041075721468053354040056307164864816082816610187421114437) * 10 ^ 70 +
        6494680029211375197990790132531344301397806320546231925771920216170087) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 136 = 0 +
    136 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 136 = 32 +
      104 by norm_num, Finset.sum_range_add]
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

theorem recurrence5B2A3_coeff_136 :
    recurrence5B2A3.coeff 136 =
      ((((144370618043277308388 * 10 ^ 70 +
        3372447334383066688414971381370629192098742530143284220779797167652409) * 10 ^ 70 +
        7220740702329997947881343880591021386065427554992045115901079876909239) * 10 ^ 70 +
        4720720975878277562351800318292683759275062883779591325286137090392278) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 137 = 0 +
    137 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
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

theorem recurrence5B2A3_coeff_137 :
    recurrence5B2A3.coeff 137 =
      -((((157658062513661282775 * 10 ^ 70 +
        1920793904961657939229273022478274534430478461654733182879607636957775) * 10 ^ 70 +
        7737345822847782224358422101459675065922083291691674816279349956563295) * 10 ^ 70 +
        2336938549152306225229814802594625015547016881030201289708329139593552) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 138 = 0 +
    138 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 138 = 32 +
      106 by norm_num, Finset.sum_range_add]
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

theorem recurrence5B2A3_coeff_138 :
    recurrence5B2A3.coeff 138 =
      ((((166762344056716780693 * 10 ^ 70 +
        6960543145130083315075783414771780007741144119517583919636535378231416) * 10 ^ 70 +
        7901639188404345458929571302002818624471581928631464282590480034101336) * 10 ^ 70 +
        3919690602877260283388819140317683551859051235274606284422007508921978) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 139 = 0 +
    139 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 139 = 32 +
      107 by norm_num, Finset.sum_range_add]
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

theorem recurrence5B2A3_coeff_139 :
    recurrence5B2A3.coeff 139 =
      -((((170590882824014378387 * 10 ^ 70 +
        9737815840506784099363960419040166163613907729864754687267483896449369) * 10 ^ 70 +
        8287348533905235352422013072149838336146367107642458456812304089136556) * 10 ^ 70 +
        6895428105233457697811559293434964313422839359499744929572642459145781) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 140 = 0 +
    140 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 140 = 32 +
      108 by norm_num, Finset.sum_range_add]
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

theorem recurrence5B2A3_coeff_140 :
    recurrence5B2A3.coeff 140 =
      ((((168419548993695574651 * 10 ^ 70 +
        3508241038239329100730772160340187263125283686511702562838349232974183) * 10 ^ 70 +
        8076925536356281041413998410833043156960732435329948658029587884617574) * 10 ^ 70 +
        3930852272818454859412452177977972657062486668165257387115742018871531) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 141 = 0 +
    141 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
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

theorem recurrence5B2A3_coeff_141 :
    recurrence5B2A3.coeff 141 =
      -((((160017342701438547922 * 10 ^ 70 +
        0018311167843735310599288082469542842050059212340881264294231684473338) * 10 ^ 70 +
        6728580672312097603594215600271553111364869781837812455996265957582434) * 10 ^ 70 +
        9974561231654818539279132479668009164225625307049923369217075244392639) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 142 = 0 +
    142 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 142 = 32 +
      110 by norm_num, Finset.sum_range_add]
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

theorem recurrence5B2A3_coeff_142 :
    recurrence5B2A3.coeff 142 =
      ((((145712214760921545215 * 10 ^ 70 +
        6674345626511948126882252879522901806690096746394354183011351264972668) * 10 ^ 70 +
        1924351367965403704086131252316059439967555478938882264143444751570134) * 10 ^ 70 +
        9721248813345807794885377637069579515266025396907085065040887603327895) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 143 = 0 +
    143 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 143 = 32 +
      111 by norm_num, Finset.sum_range_add]
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

theorem recurrence5B2A3_coeff_143 :
    recurrence5B2A3.coeff 143 =
      -((((126382018166579269386 * 10 ^ 70 +
        2026827760499010472949685444806282756299064356859343307016743210142477) * 10 ^ 70 +
        2539791698889772960488240037243156732036074262527762794594732819498791) * 10 ^ 70 +
        4715760630527660023030892395769015518229782398651547118341086745660319) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 144 = 0 +
    144 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 144 = 32 +
      112 by norm_num, Finset.sum_range_add]
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

theorem recurrence5B2A3_coeff_144 :
    recurrence5B2A3.coeff 144 =
      ((((103367643781147098129 * 10 ^ 70 +
        9170459479263420549826058987129162453166271526151088493494715694452687) * 10 ^ 70 +
        9229529705069701390761787234656721777657635390497018343935226180120831) * 10 ^ 70 +
        6827714590111332915980647844963112746530622653326902867003744522191659) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 145 = 0 +
    145 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
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

theorem recurrence5B2A3_coeff_145 :
    recurrence5B2A3.coeff 145 =
      -((((78319909481027574008 * 10 ^ 70 +
        5208212028163308003602645433014067317937149378684047708400989022500101) * 10 ^ 70 +
        6867944624563870425954980488226731467830217618665707582448389843505974) * 10 ^ 70 +
        0333618312499522236406729585889167498619316653001718755149109934396353) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 146 = 0 +
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
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_146_suffix_zero :
    (∑ x ∈ Finset.range 1,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (146 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_146 :
    recurrence5B2A3.coeff 146 =
      ((((53004408474654000522 * 10 ^ 70 +
        9611925827463304631259607920592550212110385238695884822988485853715405) * 10 ^ 70 +
        8363249434209960066376833547331526482403277669120088399250310175558818) * 10 ^ 70 +
        7638906587065482330097590106657657368990183769606574003186262685908669) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 147 = 0 +
    147 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
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
    rw [show 19 = 18 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_146_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_147_suffix_zero :
    (∑ x ∈ Finset.range 2,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (147 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_147 :
    recurrence5B2A3.coeff 147 =
      -((((29096292211474475296 * 10 ^ 70 +
        7995395455862421799620424308556576681726967162858009151072109886870227) * 10 ^ 70 +
        2452368097610724452498160421180639011728583169759208837522353401243654) * 10 ^ 70 +
        9081468877072577081150571615767587425983348096642318608005121047754502) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 148 = 0 +
    148 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 148 = 32 +
      116 by norm_num, Finset.sum_range_add]
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
    rw [show 20 = 18 +
      2 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_147_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_148_suffix_zero :
    (∑ x ∈ Finset.range 3,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (148 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_148 :
    recurrence5B2A3.coeff 148 =
      ((((7998061486996811739 * 10 ^ 70 +
        5970116549663901476634124928338779314238051669555229971510569828421100) * 10 ^ 70 +
        1752635513483929079870733529178422184386819782443593038251762053947635) * 10 ^ 70 +
        6069053840702116929421965734255470228718765317747783027686863916847972) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 149 = 0 +
    149 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 149 = 32 +
      117 by norm_num, Finset.sum_range_add]
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
    rw [show 21 = 18 +
      3 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_148_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_149_suffix_zero :
    (∑ x ∈ Finset.range 4,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (149 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_149 :
    recurrence5B2A3.coeff 149 =
      ((((9292253853043611941 * 10 ^ 70 +
        4126640789505515014455088339428447657316898297875389164229703446551006) * 10 ^ 70 +
        4205492434181869306396108664927852040067423861371389559843014253638515) * 10 ^ 70 +
        1148071367750654175445103871842545176333758916506603250684135596988842) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 150 = 0 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
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
    rw [show 22 = 18 +
      4 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_149_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_150_suffix_zero :
    (∑ x ∈ Finset.range 5,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (150 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_150 :
    recurrence5B2A3.coeff 150 =
      -((((22246061320683474256 * 10 ^ 70 +
        5393668794547888729454947044210143564376071395732400603276429693997845) * 10 ^ 70 +
        3278040113019386257273303231487459269338772814209656594109510861625449) * 10 ^ 70 +
        4624655591724150992522039412224725505515894164981709423344357174715219) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 151 = 0 +
    151 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
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
    rw [show 23 = 18 +
      5 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_150_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_151_suffix_zero :
    (∑ x ∈ Finset.range 6,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (151 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_151 :
    recurrence5B2A3.coeff 151 =
      ((((30799218932177135680 * 10 ^ 70 +
        3657011985011052484516580820163170749826102773150414082499733915962127) * 10 ^ 70 +
        9640341814901306290078182266270081156421633764949769026442555988990881) * 10 ^ 70 +
        2326476516003671517556055544850354394284603610385058742930841884954008) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 152 = 0 +
    152 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 152 = 32 +
      120 by norm_num, Finset.sum_range_add]
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
    rw [show 24 = 18 +
      6 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_151_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_152_suffix_zero :
    (∑ x ∈ Finset.range 7,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (152 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_152 :
    recurrence5B2A3.coeff 152 =
      -((((35286649927210064780 * 10 ^ 70 +
        5938946968749822792007080395809881037549378071256546389681648837344232) * 10 ^ 70 +
        3379844652405196851259849737670536688348392252154332805462928811523658) * 10 ^ 70 +
        8276295097462668905337868891017938280838384187307670278384865103203133) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 153 = 0 +
    153 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 153 = 32 +
      121 by norm_num, Finset.sum_range_add]
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
    rw [show 25 = 18 +
      7 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_152_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_153_suffix_zero :
    (∑ x ∈ Finset.range 8,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (153 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_153 :
    recurrence5B2A3.coeff 153 =
      ((((36335367073180564643 * 10 ^ 70 +
        8740709800868203458260526885325822454776542085697438869002026722070825) * 10 ^ 70 +
        3640468637505278027722624459650328232871656346019787515226151416674011) * 10 ^ 70 +
        0354743640205397931865262017943473960154870645587077069116366758693245) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 154 = 0 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
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
    rw [show 26 = 18 +
      8 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_153_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_154_suffix_zero :
    (∑ x ∈ Finset.range 9,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (154 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_154 :
    recurrence5B2A3.coeff 154 =
      -((((34739001830002142541 * 10 ^ 70 +
        3818093932589611276999254814768848368654906929977741899261727878885447) * 10 ^ 70 +
        1287023963832946808026087150321068942758686076682323873293375640999817) * 10 ^ 70 +
        3908646535344506889450701716392722297707261226206152716599365946595273) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 155 = 0 +
    155 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
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
    rw [show 27 = 18 +
      9 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_154_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_155_suffix_zero :
    (∑ x ∈ Finset.range 10,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (155 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_155 :
    recurrence5B2A3.coeff 155 =
      ((((31336077637203017449 * 10 ^ 70 +
        7341781580359141129220286914673216554953620153855359124552427894044392) * 10 ^ 70 +
        7992097449119862558512729698057320291968418683003182964491963142320765) * 10 ^ 70 +
        7032173330283439057827381038382605548217249228882921611669148441898735) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 156 = 0 +
    156 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 156 = 32 +
      124 by norm_num, Finset.sum_range_add]
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
    rw [show 28 = 18 +
      10 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_155_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_156_suffix_zero :
    (∑ x ∈ Finset.range 11,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (156 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_156 :
    recurrence5B2A3.coeff 156 =
      -((((26909320986093728586 * 10 ^ 70 +
        7066826604975513389862074553488395034637803833621632085441957375062524) * 10 ^ 70 +
        4876604160832371609060453624539476105781423562653543046546300106927094) * 10 ^ 70 +
        2899833847335148541346283485289052516742666703693083727437294103975477) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 157 = 0 +
    157 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 157 = 32 +
      125 by norm_num, Finset.sum_range_add]
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
    rw [show 29 = 18 +
      11 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_156_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_157_suffix_zero :
    (∑ x ∈ Finset.range 12,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (157 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_157 :
    recurrence5B2A3.coeff 157 =
      ((((22116083193368037019 * 10 ^ 70 +
        2026194478705153771452642752092938405657763900070086733726268838078882) * 10 ^ 70 +
        3013422084451034421510286205043346989723617886346172655164015562014163) * 10 ^ 70 +
        2427938047550740087938582762171900802109125265977705710637088259129038) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 158 = 0 +
    158 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 158 = 32 +
      126 by norm_num, Finset.sum_range_add]
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
    rw [show 30 = 18 +
      12 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_157_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_158_suffix_zero :
    (∑ x ∈ Finset.range 13,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (158 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_158 :
    recurrence5B2A3.coeff 158 =
      -((((17452429389069999126 * 10 ^ 70 +
        9968120860454475721053490833139574943119450663691138648790743560394332) * 10 ^ 70 +
        9298798142884233380352125669502636943089223771163022008936793767871471) * 10 ^ 70 +
        5131180149512333553488398338612461062182157557921678881657487603809099) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 159 = 0 +
    159 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
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
    rw [show 31 = 18 +
      13 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_158_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_159_suffix_zero :
    (∑ x ∈ Finset.range 14,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (159 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_159 :
    recurrence5B2A3.coeff 159 =
      ((((13247258230331290438 * 10 ^ 70 +
        8716252619227681912813221021675071468597523484599286534754522006805207) * 10 ^ 70 +
        7287755064554322192497297257890291037860565531302175010385291302330802) * 10 ^ 70 +
        2273620631099091691770366320711232910060438501075297474095546246651996) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 160 = 0 +
    160 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 160 = 32 +
      128 by norm_num, Finset.sum_range_add]
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
    rw [show 32 = 18 +
      14 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_159_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_160_suffix_zero :
    (∑ x ∈ Finset.range 15,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (160 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_160 :
    recurrence5B2A3.coeff 160 =
      -((((9678886761559339602 * 10 ^ 70 +
        5378004227993245050878129836532425238062389942396156436417489371305939) * 10 ^ 70 +
        9522460634210852545760406580390157778008547757229344070555787549979933) * 10 ^ 70 +
        1665119423699917090012656838575620213701304981948321781190290036700438) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 161 = 0 +
    161 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 161 = 32 +
      129 by norm_num, Finset.sum_range_add]
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
    rw [show 33 = 18 +
      15 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_160_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_161_suffix_zero :
    (∑ x ∈ Finset.range 16,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (161 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_161 :
    recurrence5B2A3.coeff 161 =
      ((((6805066291257012977 * 10 ^ 70 +
        7335403242129249112330335878309475609075967950191529975087126611599468) * 10 ^ 70 +
        6001989362806831429383138415792077157436639665900651049451419301042339) * 10 ^ 70 +
        3696276529982583461612954487572260639265892513524524648726289065302934) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 162 = 0 +
    162 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 162 = 32 +
      130 by norm_num, Finset.sum_range_add]
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
    rw [show 34 = 18 +
      16 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_161_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_162_suffix_zero :
    (∑ x ∈ Finset.range 17,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (162 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_162 :
    recurrence5B2A3.coeff 162 =
      -((((4597985963462190791 * 10 ^ 70 +
        2998370441604750016804977865580698293928875272387847360840210762129320) * 10 ^ 70 +
        2128150842778610627494369571484436692868860064287990026313181262442785) * 10 ^ 70 +
        6227388048424001071341417976218755806977783022992893560510375835440445) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 163 = 0 +
    163 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
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
    rw [show 35 = 18 +
      17 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_162_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_163_suffix_zero :
    (∑ x ∈ Finset.range 18,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (163 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_163 :
    recurrence5B2A3.coeff 163 =
      ((((2977734495562014044 * 10 ^ 70 +
        2219350957692283305333716182994404456026553244265870779068348399957940) * 10 ^ 70 +
        8873329847634508687723418370097065362066729363770365387713021283952062) * 10 ^ 70 +
        0758952129534051167051828438124372648527804370767957088745184160029385) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 164 = 0 +
    164 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 164 = 32 +
      132 by norm_num, Finset.sum_range_add]
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
    rw [show 36 = 18 +
      18 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_163_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_164_suffix_zero :
    (∑ x ∈ Finset.range 19,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (164 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_164 :
    recurrence5B2A3.coeff 164 =
      -((((1840130105970638463 * 10 ^ 70 +
        3556226536370025712746031159984295450081583175123552219770259150969334) * 10 ^ 70 +
        7271201233269408297348876391809424029772474549449166440424272935133546) * 10 ^ 70 +
        4142970868343618640813478031711842994540973318124595157545597995567222) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 165 = 0 +
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 18 +
      19 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_164_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_165_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (165 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_165_suffix_zero :
    (∑ x ∈ Finset.range 20,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (165 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_165 :
    recurrence5B2A3.coeff 165 =
      ((((1077142817055600210 * 10 ^ 70 +
        0870942636855391358285495946195376735149155116078965401257354313713951) * 10 ^ 70 +
        0139684888531211163645507811212437719040713224824340459209092464049678) * 10 ^ 70 +
        5922344635584405042124016944167592343729481189854456451103132313451389) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 166 = 1 +
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 17 +
      20 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_165_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_165_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_166_prefix_zero :
    (∑ x ∈ Finset.range 2,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (166 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (166 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_166_suffix_zero :
    (∑ x ∈ Finset.range 21,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (166 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_166 :
    recurrence5B2A3.coeff 166 =
      -((((589920634810582804 * 10 ^ 70 +
        1151869042895778006487792722750827752290959688008624347539107679189918) * 10 ^ 70 +
        8465422673372832673746516591830866850800130061255333253786587170630038) * 10 ^ 70 +
        1262740223100332872056176381604860799088126011562202157847120247814918) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 167 = 2 +
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 16 +
      21 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_166_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_166_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_167_prefix_zero :
    (∑ x ∈ Finset.range 3,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (167 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (167 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_167_suffix_zero :
    (∑ x ∈ Finset.range 22,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (167 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_167 :
    recurrence5B2A3.coeff 167 =
      ((((295545544826960237 * 10 ^ 70 +
        8375620061028405855117471097061350670942833509776737421426214323911089) * 10 ^ 70 +
        0298241592303852818995336422122648306295200596273973919252085749474534) * 10 ^ 70 +
        1025529250621122583735789808607121961433540641074868308758358297861270) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 168 = 3 +
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 15 +
      22 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_167_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_167_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_168_prefix_zero :
    (∑ x ∈ Finset.range 4,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (168 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (168 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_168_suffix_zero :
    (∑ x ∈ Finset.range 23,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (168 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_168 :
    recurrence5B2A3.coeff 168 =
      -((((129136069238719625 * 10 ^ 70 +
        7708970947275021209986305932267016744811256903160017608979692868603595) * 10 ^ 70 +
        9979124016007845442110627114082003858825567878035916508660401028677999) * 10 ^ 70 +
        4115409904970844740097236596980621980956156576343568165568354500442443) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 169 = 4 +
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 14 +
      23 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_168_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_168_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_169_prefix_zero :
    (∑ x ∈ Finset.range 5,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (169 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (169 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_169_suffix_zero :
    (∑ x ∈ Finset.range 24,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (169 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_169 :
    recurrence5B2A3.coeff 169 =
      ((((42938663291851582 * 10 ^ 70 +
        5507558784369621861603878526077763516388425726368231127393203099175687) * 10 ^ 70 +
        5687533966665894206581873776251464169300028471616984972233302506004716) * 10 ^ 70 +
        5552409958568118963546305498693136248779983694163375230668387305577826) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 170 = 5 +
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 13 +
      24 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_169_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_169_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_170_prefix_zero :
    (∑ x ∈ Finset.range 6,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (170 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (170 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_170_suffix_zero :
    (∑ x ∈ Finset.range 25,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (170 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_170 :
    recurrence5B2A3.coeff 170 =
      -((((3798591993263922 * 10 ^ 70 +
        1101732191987322226469965983307747779637821134300261239624407620183468) * 10 ^ 70 +
        5733310552205879610872571344915887491924366732187945078862297562308506) * 10 ^ 70 +
        9939740150625794618245420056660383104732261259740267272036977640275721) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 171 = 6 +
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 12 +
      25 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_170_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_170_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_171_prefix_zero :
    (∑ x ∈ Finset.range 7,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (171 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (171 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_171_suffix_zero :
    (∑ x ∈ Finset.range 26,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (171 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_171 :
    recurrence5B2A3.coeff 171 =
      -((((9964290086495450 * 10 ^ 70 +
        4886812379638302480619127111432388309277600916234528634502517520262377) * 10 ^ 70 +
        7511155888245078047700499959315953487779370432595060955103399151578186) * 10 ^ 70 +
        0614647900210431634269262398170818269553738438058024728593794132508815) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 172 = 7 +
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 11 +
      26 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_171_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_171_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_172_prefix_zero :
    (∑ x ∈ Finset.range 8,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (172 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (172 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_172_suffix_zero :
    (∑ x ∈ Finset.range 27,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (172 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_172 :
    recurrence5B2A3.coeff 172 =
      ((((11614347209406440 * 10 ^ 70 +
        7467903802161495642947840273525598629847355584605485052421321608947728) * 10 ^ 70 +
        7750694660746558239119792322541372818965083261145835116194372650181773) * 10 ^ 70 +
        1427685171878184573629022825785351746572473803848431925862248247980085) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 173 = 8 +
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 10 +
      27 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_172_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_172_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_173_prefix_zero :
    (∑ x ∈ Finset.range 9,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (173 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (173 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_173_suffix_zero :
    (∑ x ∈ Finset.range 28,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (173 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_173 :
    recurrence5B2A3.coeff 173 =
      -((((8635590250451800 * 10 ^ 70 +
        1748517495855765187778672329619050379208419328790435714073641970378097) * 10 ^ 70 +
        8362817079015011443204075306313803799761894826357163647541981113541434) * 10 ^ 70 +
        9709728004399398187399266899794296227036172443270280551564255972200077) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 174 = 9 +
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 9 +
      28 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_173_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_173_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_174_prefix_zero :
    (∑ x ∈ Finset.range 10,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (174 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (174 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_174_suffix_zero :
    (∑ x ∈ Finset.range 29,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (174 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_174 :
    recurrence5B2A3.coeff 174 =
      ((((4804518517760279 * 10 ^ 70 +
        3719427902249051769984849148593519220559198539507836892732511436856961) * 10 ^ 70 +
        7645869161216947011962984640767164852127514592103138952850871917689413) * 10 ^ 70 +
        8434622767078863414054119311680898669403749711261369627651315853830431) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 175 = 10 +
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 8 +
      29 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_174_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_174_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_175_prefix_zero :
    (∑ x ∈ Finset.range 11,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (175 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (175 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_175_suffix_zero :
    (∑ x ∈ Finset.range 30,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (175 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_175 :
    recurrence5B2A3.coeff 175 =
      -((((1700153944919593 * 10 ^ 70 +
        1303228751228143154972789103399999704644353472736512125836102183673238) * 10 ^ 70 +
        3596346141986460874338078584853323768625561553625083253840308792614132) * 10 ^ 70 +
        6066040642171526218556771852857617918414332117579906055363831850394492) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 176 = 11 +
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 7 +
      30 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_175_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_175_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_176_prefix_zero :
    (∑ x ∈ Finset.range 12,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (176 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (176 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_176_suffix_zero :
    (∑ x ∈ Finset.range 31,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (176 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_176 :
    recurrence5B2A3.coeff 176 =
      -((((273807457213637 * 10 ^ 70 +
        9533587877892804150006033595874274282992427754880542822431311742172662) * 10 ^ 70 +
        3272566500350764975255731090323661083808506230281214333654004593191879) * 10 ^ 70 +
        1544031702402574943366875376097273972673202590701346170512831396219438) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 177 = 12 +
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 6 +
      31 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_176_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_176_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_177_prefix_zero :
    (∑ x ∈ Finset.range 13,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (177 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (177 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_177_suffix_zero :
    (∑ x ∈ Finset.range 32,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (177 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_177 :
    recurrence5B2A3.coeff 177 =
      ((((1249746337629726 * 10 ^ 70 +
        3251305464378004495496934902177216395473189086886848387695994059172227) * 10 ^ 70 +
        7676206281752787194539439557636675472072396621861014592672334717577478) * 10 ^ 70 +
        8556870559122917861906268726490850700864648955720523566261390184635516) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 178 = 13 +
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 5 +
      32 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_177_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_177_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_178_prefix_zero :
    (∑ x ∈ Finset.range 14,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (178 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (178 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_178_suffix_zero :
    (∑ x ∈ Finset.range 33,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (178 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_178 :
    recurrence5B2A3.coeff 178 =
      -((((1533122808269340 * 10 ^ 70 +
        3039941496092612657966023249803460431997857211763442687004985087908440) * 10 ^ 70 +
        7032365459016582136140395929379203143378120027935148859446144319665775) * 10 ^ 70 +
        7212075808283725070924919466075255726987066409072228199962497891941729) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 179 = 14 +
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 4 +
      33 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_178_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_178_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_179_prefix_zero :
    (∑ x ∈ Finset.range 15,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (179 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (179 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_179_suffix_zero :
    (∑ x ∈ Finset.range 34,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (179 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_179 :
    recurrence5B2A3.coeff 179 =
      ((((1422895393243076 * 10 ^ 70 +
        1060655786634562774186528664415067553332401562923037936283562397203627) * 10 ^ 70 +
        4511328209314206838238331445387295206132438904548510391085017153157230) * 10 ^ 70 +
        9350257909828823085519090602960879992475667469044728445891170983450390) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 180 = 15 +
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 3 +
      34 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_179_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_179_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_180_prefix_zero :
    (∑ x ∈ Finset.range 16,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (180 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (180 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_180_suffix_zero :
    (∑ x ∈ Finset.range 35,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (180 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_180 :
    recurrence5B2A3.coeff 180 =
      -((((1142780404012983 * 10 ^ 70 +
        1868106735158263860236220093201600789951923427098617896352405923405576) * 10 ^ 70 +
        1662588401541691395456451152217384148378782724650789469670493666163239) * 10 ^ 70 +
        8435987974335600761052915172794059133190547547994745085802108313853825) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 181 = 16 +
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 2 +
      35 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_180_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_180_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_181_prefix_zero :
    (∑ x ∈ Finset.range 17,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (181 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (181 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_181_suffix_zero :
    (∑ x ∈ Finset.range 36,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (181 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_181 :
    recurrence5B2A3.coeff 181 =
      ((((831692892770933 * 10 ^ 70 +
        9838406854555735707307116055137756715977769977821716451184225308698500) * 10 ^ 70 +
        5713730819445154502097407353070204348915202391509385058112553754589470) * 10 ^ 70 +
        7874784021722173901274362381969889969220893823906184163454345481825717) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 182 = 17 +
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 1 +
      36 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_181_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_181_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_182_prefix_zero :
    (∑ x ∈ Finset.range 18,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (182 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (182 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_182_suffix_zero :
    (∑ x ∈ Finset.range 37,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (182 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_182 :
    recurrence5B2A3.coeff 182 =
      -((((559996543992191 * 10 ^ 70 +
        2137880438968606639565601097837948926481344843499177733692622839504454) * 10 ^ 70 +
        3188598713540091255718969877813515485582376937531081626384534944339593) * 10 ^ 70 +
        8181964433682236648926969864747116148463943979765949881198291383739229) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 183 = 18 +
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_182_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_182_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_183_prefix_zero :
    (∑ x ∈ Finset.range 19,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (183 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (183 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_183_suffix_zero :
    (∑ x ∈ Finset.range 38,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (183 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_183 :
    recurrence5B2A3.coeff 183 =
      ((((352382914316756 * 10 ^ 70 +
        3106620601373648582056319184045735706894697796334385558924104842885649) * 10 ^ 70 +
        5816551977432280702509403094929565729093663377862418109204820111968631) * 10 ^ 70 +
        4176413435967663861397936819748140951606256426926068618828406084644472) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 184 = 19 +
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
    rw [show 69 = 31 +
      38 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_183_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_183_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_184_prefix_zero :
    (∑ x ∈ Finset.range 20,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (184 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (184 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_184_suffix_zero :
    (∑ x ∈ Finset.range 39,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (184 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_184 :
    recurrence5B2A3.coeff 184 =
      -((((208084786633657 * 10 ^ 70 +
        4259707813135106901587758027756676093703084081615531687088374922480671) * 10 ^ 70 +
        4933968142979061432206904716657867142669796555364968241689550493351144) * 10 ^ 70 +
        1100194931656596142080724680886447276173058246727832415068237550375410) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 185 = 20 +
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
    rw [show 69 = 30 +
      39 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_184_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_184_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_185_prefix_zero :
    (∑ x ∈ Finset.range 21,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (185 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (185 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_185_suffix_zero :
    (∑ x ∈ Finset.range 40,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (185 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_185 :
    recurrence5B2A3.coeff 185 =
      ((((115245238534358 * 10 ^ 70 +
        2916853538500727252279382743964083076178241870300013639110010579860846) * 10 ^ 70 +
        1530942092169338702952386424081532692299415792940370018323032966455908) * 10 ^ 70 +
        4685001977229890997816603122055160331743237229620220467976006266308174) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 186 = 21 +
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
    rw [show 69 = 29 +
      40 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_185_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_185_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_186_prefix_zero :
    (∑ x ∈ Finset.range 22,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (186 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (186 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_186_suffix_zero :
    (∑ x ∈ Finset.range 41,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (186 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_186 :
    recurrence5B2A3.coeff 186 =
      -((((59509068720985 * 10 ^ 70 +
        6487549448428391460378161674886199236151323415658705760665528626093926) * 10 ^ 70 +
        3464669180982536835873937381267315928259206997565842478941074071956109) * 10 ^ 70 +
        4336559784672732381689172319466850712574539089720222647578098768999050) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 187 = 22 +
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
    rw [show 69 = 28 +
      41 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_186_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_186_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_187_prefix_zero :
    (∑ x ∈ Finset.range 23,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (187 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (187 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_187_suffix_zero :
    (∑ x ∈ Finset.range 42,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (187 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_187 :
    recurrence5B2A3.coeff 187 =
      ((((28226426042342 * 10 ^ 70 +
        5869179443661848573755372548601939779819151544216997940098678407802356) * 10 ^ 70 +
        2383078414116010728829126866725007532620740749093572902030816007232982) * 10 ^ 70 +
        8623215895216636834168704349290202153130852133216122537943390734827860) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 188 = 23 +
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
    rw [show 69 = 27 +
      42 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_187_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_187_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_188_prefix_zero :
    (∑ x ∈ Finset.range 24,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (188 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (188 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_188_suffix_zero :
    (∑ x ∈ Finset.range 43,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (188 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_188 :
    recurrence5B2A3.coeff 188 =
      -((((11875026520815 * 10 ^ 70 +
        1360188031497922287397615722232991211272513013007608211991526178273777) * 10 ^ 70 +
        8861179274758561386342123086035285703713189211814702911190215397970297) * 10 ^ 70 +
        1596350281992745606129421693705757731809129850418290199379578030696172) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 189 = 24 +
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
    rw [show 69 = 26 +
      43 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_188_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_188_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_189_prefix_zero :
    (∑ x ∈ Finset.range 25,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (189 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (189 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_189_suffix_zero :
    (∑ x ∈ Finset.range 44,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (189 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_189 :
    recurrence5B2A3.coeff 189 =
      ((((4012764492363 * 10 ^ 70 +
        0377430900950862728834502284605279396705546973687948504916936943523187) * 10 ^ 70 +
        3141838044715843148733058852698701120574778764349126742476171922158863) * 10 ^ 70 +
        4221460128804175163184934220075247494567333515652393616455248082608749) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 190 = 25 +
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
    rw [show 69 = 25 +
      44 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_189_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_189_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_190_prefix_zero :
    (∑ x ∈ Finset.range 26,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (190 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (190 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_190_suffix_zero :
    (∑ x ∈ Finset.range 45,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (190 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_190 :
    recurrence5B2A3.coeff 190 =
      -((((637740799541 * 10 ^ 70 +
        6829337798901231008055332391320472231408112321712985598376510873353945) * 10 ^ 70 +
        2449139227409918442716354397375834803800662191599150350985647950439319) * 10 ^ 70 +
        7177534473350100227065471518569895785110400214695636158511299106677571) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 191 = 26 +
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
    rw [show 69 = 24 +
      45 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_190_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_190_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_191_prefix_zero :
    (∑ x ∈ Finset.range 27,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (191 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (191 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_191_suffix_zero :
    (∑ x ∈ Finset.range 46,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (191 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_191 :
    recurrence5B2A3.coeff 191 =
      -((((553562745379 * 10 ^ 70 +
        0224834889361838679011531114772306170240597166740707499991560907037237) * 10 ^ 70 +
        3943975931900459621879894308877305395836852752017157365722489938853346) * 10 ^ 70 +
        1599962829393173744170093031788043248484481306703204984487466732250014) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 192 = 27 +
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
    rw [show 69 = 23 +
      46 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_191_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_191_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_192_prefix_zero :
    (∑ x ∈ Finset.range 28,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (192 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (192 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_192_suffix_zero :
    (∑ x ∈ Finset.range 47,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (192 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_192 :
    recurrence5B2A3.coeff 192 =
      ((((791147051783 * 10 ^ 70 +
        2614130065297292968203636780930294886809727383963883715193752936368252) * 10 ^ 70 +
        6851084196852072087469976550556441025761602545597603666380434314024117) * 10 ^ 70 +
        8005314797131524400097646768616310456453090082880479198941429330579330) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 193 = 28 +
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
    rw [show 69 = 22 +
      47 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_192_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_192_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_193_prefix_zero :
    (∑ x ∈ Finset.range 29,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (193 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (193 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_193_suffix_zero :
    (∑ x ∈ Finset.range 48,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (193 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_193 :
    recurrence5B2A3.coeff 193 =
      -((((679907189728 * 10 ^ 70 +
        0540970921001196055619278038513352406153192163910092774251828403601530) * 10 ^ 70 +
        3846631964686254119887000087656320421181495985477465649476954782300473) * 10 ^ 70 +
        1050500036095072821743301453523146400804949697017956052265001221130277) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 194 = 29 +
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
    rw [show 69 = 21 +
      48 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_193_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_193_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_194_prefix_zero :
    (∑ x ∈ Finset.range 30,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (194 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (194 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_194_suffix_zero :
    (∑ x ∈ Finset.range 49,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (194 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_194 :
    recurrence5B2A3.coeff 194 =
      ((((487965919058 * 10 ^ 70 +
        1109305376975709931795501639046729146181611178269447490797363442852194) * 10 ^ 70 +
        5995185731389675032312386232722538713906437564304327531124747856413884) * 10 ^ 70 +
        6962259221012392555341984260368734241549114933016556062166833578066670) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 195 = 30 +
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
    rw [show 69 = 20 +
      49 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_194_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_194_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_195_prefix_zero :
    (∑ x ∈ Finset.range 31,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (195 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (195 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_195_suffix_zero :
    (∑ x ∈ Finset.range 50,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (195 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_195 :
    recurrence5B2A3.coeff 195 =
      -((((316334678791 * 10 ^ 70 +
        5631056189221049116183091294457188654763183828148852256737357442178458) * 10 ^ 70 +
        4419644912644108694759949802842893140786837237934523811679066669045330) * 10 ^ 70 +
        4692597031485957068773364072184164669424202373202983103560196685390958) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 196 = 31 +
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
    rw [show 69 = 19 +
      50 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_195_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_195_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_196_prefix_zero :
    (∑ x ∈ Finset.range 32,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (196 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (196 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_196_suffix_zero :
    (∑ x ∈ Finset.range 51,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (196 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_196 :
    recurrence5B2A3.coeff 196 =
      ((((191004179411 * 10 ^ 70 +
        0384231703470269965223739389725277060290520616174273798129853473018883) * 10 ^ 70 +
        5712037787362068054622811035132391650702801602968925833193088068069622) * 10 ^ 70 +
        1309804990076878389439409163530419603851373329955841934539734115923686) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 197 = 32 +
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
    rw [show 69 = 18 +
      51 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_196_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_196_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_197_prefix_zero :
    (∑ x ∈ Finset.range 33,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (197 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (197 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_197_suffix_zero :
    (∑ x ∈ Finset.range 52,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (197 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_197 :
    recurrence5B2A3.coeff 197 =
      -((((108981784147 * 10 ^ 70 +
        8928654090943987705025682533593087717076242567929845141407487420083327) * 10 ^ 70 +
        7898180848202491891789784612173053343055624470677168962264224057982300) * 10 ^ 70 +
        0664161491024038366065400976194701299008391472240593698533047366367442) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 198 = 33 +
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
    rw [show 69 = 17 +
      52 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_197_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_197_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_198_prefix_zero :
    (∑ x ∈ Finset.range 34,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (198 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (198 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_198_suffix_zero :
    (∑ x ∈ Finset.range 53,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (198 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_198 :
    recurrence5B2A3.coeff 198 =
      ((((59186381141 * 10 ^ 70 +
        3059510932837058656265463850347801081333181208969978847233402859080165) * 10 ^ 70 +
        8730522442371465483789390094891990215687603166332371927771251677519349) * 10 ^ 70 +
        3454791079584344410806748685230037875786002055631059846384217309339870) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 199 = 34 +
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
    rw [show 69 = 16 +
      53 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_198_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_198_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_199_prefix_zero :
    (∑ x ∈ Finset.range 35,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (199 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (199 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_199_suffix_zero :
    (∑ x ∈ Finset.range 54,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (199 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_199 :
    recurrence5B2A3.coeff 199 =
      -((((30700349678 * 10 ^ 70 +
        6240082259299287476597035219522053147788877976337676117583795441106232) * 10 ^ 70 +
        0810956993985941530340328562951877175705001480320485742963611198692779) * 10 ^ 70 +
        2523139526717817436739948922494207631268829566334102151781496259845944) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 200 = 35 +
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
    rw [show 69 = 15 +
      54 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_199_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_199_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_200_prefix_zero :
    (∑ x ∈ Finset.range 36,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (200 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (200 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_200_suffix_zero :
    (∑ x ∈ Finset.range 55,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (200 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_200 :
    recurrence5B2A3.coeff 200 =
      ((((15228480955 * 10 ^ 70 +
        3762539379204706327467904055605776383078986479790941976223585914045211) * 10 ^ 70 +
        4103482237028659183293245831190906276827002931817231001156449845147930) * 10 ^ 70 +
        9640766819751873013519797343661933175373303399246678819332609726115262) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 201 = 36 +
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
    rw [show 69 = 14 +
      55 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_200_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_200_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_201_prefix_zero :
    (∑ x ∈ Finset.range 37,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (201 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (201 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_201_suffix_zero :
    (∑ x ∈ Finset.range 56,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (201 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_201 :
    recurrence5B2A3.coeff 201 =
      -((((7223001046 * 10 ^ 70 +
        7767404090394287630905603426214570721133901714678625938294476786311159) * 10 ^ 70 +
        3331111897050182560829960254365480578460494348826772091586731377981378) * 10 ^ 70 +
        7985428895537705892887307152018985255883066461760362974085781883948190) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 202 = 37 +
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
    rw [show 69 = 13 +
      56 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_201_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_201_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_202_prefix_zero :
    (∑ x ∈ Finset.range 38,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (202 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (202 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_202_suffix_zero :
    (∑ x ∈ Finset.range 57,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (202 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_202 :
    recurrence5B2A3.coeff 202 =
      ((((3273192663 * 10 ^ 70 +
        6693181415517279169060815810370644662139048406985032928403001550491130) * 10 ^ 70 +
        8369769335788572192181469499656657724846940084677475043455599799607890) * 10 ^ 70 +
        4886251051686034241672677497451159046786861453190755244909915543583070) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 203 = 38 +
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
    rw [show 69 = 12 +
      57 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_202_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_202_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_203_prefix_zero :
    (∑ x ∈ Finset.range 39,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (203 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (203 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_203_suffix_zero :
    (∑ x ∈ Finset.range 58,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (203 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_203 :
    recurrence5B2A3.coeff 203 =
      -((((1415976056 * 10 ^ 70 +
        3596193485812195796989242817991533369681595605644689051041535875520042) * 10 ^ 70 +
        8075598903560876667466849186271569718633689695488763692472028751086044) * 10 ^ 70 +
        9752409758998293821844978403143553011013880435298677266738597249968317) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 204 = 39 +
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
    rw [show 69 = 11 +
      58 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_203_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_203_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_204_prefix_zero :
    (∑ x ∈ Finset.range 40,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (204 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (204 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_204_suffix_zero :
    (∑ x ∈ Finset.range 59,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (204 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_204 :
    recurrence5B2A3.coeff 204 =
      ((((584949954 * 10 ^ 70 +
        8998598442698872612662394309303487555058133519335397325275973199252544) * 10 ^ 70 +
        8155113466008229339480436138811174209018105526239486611000324012206463) * 10 ^ 70 +
        5617625777146945952254776252998617003901443011826631072816097595133108) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 205 = 40 +
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
    rw [show 69 = 10 +
      59 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_204_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_204_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_205_prefix_zero :
    (∑ x ∈ Finset.range 41,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (205 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (205 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_205_suffix_zero :
    (∑ x ∈ Finset.range 60,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (205 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_205 :
    recurrence5B2A3.coeff 205 =
      -((((231671320 * 10 ^ 70 +
        7430589634659818635101964262398158825311442363882586991124962053510498) * 10 ^ 70 +
        6744647959781755533930982112846220996006438461726688404814085869796010) * 10 ^ 70 +
        7185221055008654707760862940948146814984575589573055228257660201714326) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 206 = 41 +
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
    rw [show 69 = 9 +
      60 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_205_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_205_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_206_prefix_zero :
    (∑ x ∈ Finset.range 42,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (206 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (206 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_206_suffix_zero :
    (∑ x ∈ Finset.range 61,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (206 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_206 :
    recurrence5B2A3.coeff 206 =
      ((((89064932 * 10 ^ 70 +
        6196776714131466090016869479495838085831466122299628508659612991390329) * 10 ^ 70 +
        7547357581053795778981422791067990707519610453232150218039590137943825) * 10 ^ 70 +
        9964534410959329274987815684055004397332680212882339460794893495493575) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 207 = 42 +
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
    rw [show 69 = 8 +
      61 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_206_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_206_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_207_prefix_zero :
    (∑ x ∈ Finset.range 43,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (207 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (207 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_207_suffix_zero :
    (∑ x ∈ Finset.range 62,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (207 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_207 :
    recurrence5B2A3.coeff 207 =
      -((((34209280 * 10 ^ 70 +
        1221770088766626440887686728469665080450931069360758176538169870109358) * 10 ^ 70 +
        7504779399429640522150884908019458594496472321587737344181884040037089) * 10 ^ 70 +
        4492662972987118044588946562614080986621948260965031399709413986696916) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 208 = 43 +
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
    rw [show 69 = 7 +
      62 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_207_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_207_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_208_prefix_zero :
    (∑ x ∈ Finset.range 44,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (208 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (208 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_208_suffix_zero :
    (∑ x ∈ Finset.range 63,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (208 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_208 :
    recurrence5B2A3.coeff 208 =
      ((((13812153 * 10 ^ 70 +
        3744063093435506570632420583117931533614298169902042156109049681662335) * 10 ^ 70 +
        0155255044648451325094645690026228748779993630027201536784496106764875) * 10 ^ 70 +
        9709373438082877059762337442998982445923040727177217319654653608362568) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 209 = 44 +
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
  rw [recurrence5B2A3_coeff_208_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_208_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_209_prefix_zero :
    (∑ x ∈ Finset.range 45,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (209 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (209 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_209_suffix_zero :
    (∑ x ∈ Finset.range 64,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (209 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_209 :
    recurrence5B2A3.coeff 209 =
      -((((6204201 * 10 ^ 70 +
        1031196967946206277302966929713269342520781038107705254914321251451857) * 10 ^ 70 +
        1933271522863414292290852658479150097163687939603425487626231688550739) * 10 ^ 70 +
        3972604820159112800121525000335913905781766471379066650983577734244600) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 210 = 45 +
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
  rw [recurrence5B2A3_coeff_209_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_209_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_210_prefix_zero :
    (∑ x ∈ Finset.range 46,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (210 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (210 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_210_suffix_zero :
    (∑ x ∈ Finset.range 65,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (210 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_210 :
    recurrence5B2A3.coeff 210 =
      ((((3155854 * 10 ^ 70 +
        0143775695949349263134505994185985735809903745572906961210453875212874) * 10 ^ 70 +
        7069945440020243303570349353050017185114705841512871280219000750178832) * 10 ^ 70 +
        7261955632183353065030477954753658604388499673083568453541587653114657) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 211 = 46 +
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
  rw [recurrence5B2A3_coeff_210_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_210_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_211_prefix_zero :
    (∑ x ∈ Finset.range 47,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (211 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (211 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_211_suffix_zero :
    (∑ x ∈ Finset.range 66,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (211 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_211 :
    recurrence5B2A3.coeff 211 =
      -((((1747244 * 10 ^ 70 +
        6604792074604942990573296254067081806474718131921922184472786305371167) * 10 ^ 70 +
        6231418425670038411497811415986801337322646303659300374838908426610233) * 10 ^ 70 +
        3523790488155184757938860601819947966376283661633860296277210770838730) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 212 = 47 +
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
  rw [recurrence5B2A3_coeff_211_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_211_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_212_prefix_zero :
    (∑ x ∈ Finset.range 48,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (212 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (212 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_212_suffix_zero :
    (∑ x ∈ Finset.range 67,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (212 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_212 :
    recurrence5B2A3.coeff 212 =
      ((((993351 * 10 ^ 70 +
        3946839383434243221338638972341676530757970481578678319460788909343659) * 10 ^ 70 +
        0088729787418643478852082688381514973404429421125179622637907854862626) * 10 ^ 70 +
        4269712500069810794952489523805305607415848631528705805525712045709437) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 213 = 48 +
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
  rw [recurrence5B2A3_coeff_212_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_212_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_213_prefix_zero :
    (∑ x ∈ Finset.range 49,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (213 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (213 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_213_suffix_zero :
    (∑ x ∈ Finset.range 68,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (213 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_213 :
    recurrence5B2A3.coeff 213 =
      -((((556442 * 10 ^ 70 +
        3163051700850701796681576669069334507688303584340600953737772380942451) * 10 ^ 70 +
        0892915176593928555277795403985470687702784775536261627587406581067392) * 10 ^ 70 +
        6952273621517187217560628396777978879084116803483246748267971723027064) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 214 = 49 +
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
  rw [recurrence5B2A3_coeff_213_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_213_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_214_prefix_zero :
    (∑ x ∈ Finset.range 50,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (214 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (214 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_214_suffix_zero :
    (∑ x ∈ Finset.range 69,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (214 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_214 :
    recurrence5B2A3.coeff 214 =
      ((((300906 * 10 ^ 70 +
        3174901380127088969569000581074614280756289789191058032863202283602536) * 10 ^ 70 +
        5731061802906432264557300351485393257656086050038931080610814839837382) * 10 ^ 70 +
        2219464342585982712387756918155028677897990967506483272586796673966607) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 215 = 50 +
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
  rw [recurrence5B2A3_coeff_214_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_214_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_215_prefix_zero :
    (∑ x ∈ Finset.range 51,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (215 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (215 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_215_suffix_zero :
    (∑ x ∈ Finset.range 70,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (215 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_215 :
    recurrence5B2A3.coeff 215 =
      -((((155894 * 10 ^ 70 +
        8907009656679085608086838223970877966952468679472345746076778083914631) * 10 ^ 70 +
        3809388396013125537776987996605691235506266438985661691955841223180769) * 10 ^ 70 +
        6453287495727374737058160968484301557361824617143917726766042912405678) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 216 = 51 +
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
  rw [recurrence5B2A3_coeff_215_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_215_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_216_prefix_zero :
    (∑ x ∈ Finset.range 52,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (216 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (216 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_216_suffix_zero :
    (∑ x ∈ Finset.range 71,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (216 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_216 :
    recurrence5B2A3.coeff 216 =
      ((((77262 * 10 ^ 70 +
        9601544337318447748566123922125662583393772523120514705331437939944674) * 10 ^ 70 +
        4773343444367142708463126145017642510812177779452585137688421312041120) * 10 ^ 70 +
        0164443704340924315427292495750596621337162133555472127011263032717329) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 217 = 52 +
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
  rw [recurrence5B2A3_coeff_216_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_216_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_217_prefix_zero :
    (∑ x ∈ Finset.range 53,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (217 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (217 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_217_suffix_zero :
    (∑ x ∈ Finset.range 72,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (217 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_217 :
    recurrence5B2A3.coeff 217 =
      -((((36667 * 10 ^ 70 +
        6121344507718293062894073448914756448777551401784330587430342360471543) * 10 ^ 70 +
        1080684356790561157528417933985036705313390996954296575029191235981090) * 10 ^ 70 +
        8491637660691037799403738615710162817622475601925667027498415609811366) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 218 = 53 +
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
  rw [recurrence5B2A3_coeff_217_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_217_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
