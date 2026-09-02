/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupB2
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupA3
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupB2A3Part0Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 5 lookup certificate: B2A3 coefficient convolution

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
