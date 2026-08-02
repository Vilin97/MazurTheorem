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

theorem recurrence5A3Square_coeff_0 :
    recurrence5A3Square.coeff 0 =
      (1991736184768556757067297520080351110144 : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_1 :
    recurrence5A3Square.coeff 1 =
      (-9036463261630469368763073641158639200241152 : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_2 :
    recurrence5A3Square.coeff 2 =
      (18064741864868393440837050553290172313227319232 : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_3 :
    recurrence5A3Square.coeff 3 =
      (-19324108267339265632890147311613641594611141544736 : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_4 :
    recurrence5A3Square.coeff 4 =
      (11802588115344033610155269205881050753270416345852996 : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_5 :
    recurrence5A3Square.coeff 5 =
      (-4642674962150601132922654272565746747188228265321914520 : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_6 :
    recurrence5A3Square.coeff 6 =
      (2175363362830863940476793015128798726321045482765981050716 : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_7 :
    recurrence5A3Square.coeff 7 =
      (-993346042544979332136818180009489721230978674346549152633776 : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_8 :
    recurrence5A3Square.coeff 8 =
      (183620322140136516393719746295159399973300820408504838494563508 : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_9 :
    recurrence5A3Square.coeff 9 =
      (91084765655181320657888066612453662374617917723987602986580807076 : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_10 :
    recurrence5A3Square.coeff 10 =
      (-81393749859215420067111513785731244142068545513821536189128484032716 : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_11 :
    recurrence5A3Square.coeff 11 =
      ((3 * 10 ^ 70 +
        7637706346053028645112690541114955255077046774933892598435862743346936) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_12 :
    recurrence5A3Square.coeff 12 =
      -((1590 * 10 ^ 70 +
        8723365212487610163802266923527133200593549609968628081498103069842096) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_13 :
    recurrence5A3Square.coeff 13 =
      ((621074 * 10 ^ 70 +
        1351158090884028011253995480811736860508828997365170634855645376851084) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_14 :
    recurrence5A3Square.coeff 14 =
      -((166450582 * 10 ^ 70 +
        3605097591348133179468048042033904167907031404191508775846429354786111) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_15 :
    recurrence5A3Square.coeff 15 =
      ((7543846123 * 10 ^ 70 +
        8334319333988075588859692798925588658853238352142717683367152351077242) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_16 :
    recurrence5A3Square.coeff 16 =
      ((17509441081551 * 10 ^ 70 +
        7798199033656443336770392226412570264486761272685110279467072166606713) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_17 :
    recurrence5A3Square.coeff 17 =
      -((9942697889984245 * 10 ^ 70 +
        0158247506024025344476138327578832025203928300939238416424705630823846) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_18 :
    recurrence5A3Square.coeff 18 =
      ((3287694666803357455 * 10 ^ 70 +
        1389358036731827367590588245785640279210513562310543061345006489199318) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_19 :
    recurrence5A3Square.coeff 19 =
      -((779167558967609905930 * 10 ^ 70 +
        8581808123955102041046151845121004744581015577768528577082629928299216) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_20 :
    recurrence5A3Square.coeff 20 =
      ((139275052861061560623756 * 10 ^ 70 +
        2598758674519134487041777565551619287663394645434607976427860234442031) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_21 :
    recurrence5A3Square.coeff 21 =
      -((18654923187388693606948207 * 10 ^ 70 +
        8619298648530190537819973614468492423997010452514000862695339164798110) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_22 :
    recurrence5A3Square.coeff 22 =
      ((1709117534918668108243101790 * 10 ^ 70 +
        8335458132460587930592825060056541304266945031664927665113541688557642) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_23 :
    recurrence5A3Square.coeff 23 =
      -((57101255709259215339688433644 * 10 ^ 70 +
        7566198959727099731173177271541048798511643618601935720409841738287716) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_24 :
    recurrence5A3Square.coeff 24 =
      -((13808590663632299237984798978636 * 10 ^ 70 +
        2445798406638283214190151920310442524065231677140804712298161383191878) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_25 :
    recurrence5A3Square.coeff 25 =
      ((3380326577409046574716735872749196 * 10 ^ 70 +
        3992019085393602879747599381737664192644569150175531032230535714242276) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_26 :
    recurrence5A3Square.coeff 26 =
      -((446699496885062070738758222439535660 * 10 ^ 70 +
        2273177577707747746136510322282853062755179124896382416512536796643665) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_27 :
    recurrence5A3Square.coeff 27 =
      ((41018973064175823597972865941976444230 * 10 ^ 70 +
        3347531450206665141811429888178760610401840989761462381809108290756540) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_28 :
    recurrence5A3Square.coeff 28 =
      -((2501230562759208612736587526972667108140 * 10 ^ 70 +
        3613407374212020976123114088870870915423645191997627364330391701897670) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_29 :
    recurrence5A3Square.coeff 29 =
      ((44262071216989959558112385784013443931931 * 10 ^ 70 +
        1953667550473496597852315272118998422139093206392047747114481056150890) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_30 :
    recurrence5A3Square.coeff 30 =
      ((12497260086610676206216989454037689320051099 * 10 ^ 70 +
        4476081623049180791230493165636542040520167716176603408591260637880605) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_31 :
    recurrence5A3Square.coeff 31 =
      -((2128425869964095548987571554219863706182081407 * 10 ^ 70 +
        3516828423646438897419352263507750922619768829887576925817675931466710) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_32 :
    recurrence5A3Square.coeff 32 =
      ((221263121888724507797803419036141927958841292981 * 10 ^ 70 +
        7954891285576576481154151203758381082077949016233498784157701000020578) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_33 :
    recurrence5A3Square.coeff 33 =
      -((18036717320149191057814514417800093743917091259147 * 10 ^ 70 +
        6609359308622226887489731353166208036119458979498389248478757651885376) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_34 :
    recurrence5A3Square.coeff 34 =
      ((1238385999100145073419378117639036187652909722200522 * 10 ^ 70 +
        8521212333289694765776407500076242202377262146570670476441532995562071) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_35 :
    recurrence5A3Square.coeff 35 =
      -((73933644769880433328301630099587671281748214976114755 * 10 ^ 70 +
        1372101125291796773959024914567702155541062654009757924618341637935390) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_36 :
    recurrence5A3Square.coeff 36 =
      ((3905842687640756919354348591712370907259390021427481098 * 10 ^ 70 +
        7665529904269693197960567378622965330943546029790507051590579142509330) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_37 :
    recurrence5A3Square.coeff 37 =
      -((184568031786403166012672323386376333264792728395315873257 * 10 ^ 70 +
        1614351513665394785410985170090633518661836965648230512287262159872792) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_38 :
    recurrence5A3Square.coeff 38 =
      ((7856332142681586192696515327030624476909959076426972072051 * 10 ^ 70 +
        2708563103381287189069304297051755937626221347859776236176655253057449) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_39 :
    recurrence5A3Square.coeff 39 =
      -((302615200448093469831279070611371901656787135313951859111092 * 10 ^ 70 +
        3662458259861731643262194264220018209322955414468654178940884232187774) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_40 :
    recurrence5A3Square.coeff 40 =
      ((10576221659974862925436344525502557092409958658009658280236713 * 10 ^ 70 +
        9633114156025153593556855907315708485123655846999869498088093264379306) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_41 :
    recurrence5A3Square.coeff 41 =
      -((335684229826703897965298438093960749490740920398015090996715245 * 10 ^ 70 +
        8865704440262144005006595211165310808328969713792891661424481165523058) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_42 :
    recurrence5A3Square.coeff 42 =
      ((9665084347623854735151218080855346053302129456878855483078663627 * 10 ^ 70 +
        9581757976099154946391088000202170401678522910750491096397494386521362) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_43 :
    recurrence5A3Square.coeff 43 =
      -((251452402721286714908653431758715380198674056945260859978069851027 * 10 ^ 70 +
        8177228327620953550891714378083325678741294057140577718072473421853374) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_44 :
    recurrence5A3Square.coeff 44 =
      ((5861253797936143103574475236119688592975382481890859338803625071091 * 10 ^ 70 +
        1662375150163152103767321160842383302585237077056314718064356601162018) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_45 :
    recurrence5A3Square.coeff 45 =
      -((120292001687801859253761316006275253541304633577098676006926495760671 * 10 ^ 70 +
        6349338342697719095524390754496056339849356739086840614488370724642044) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_46 :
    recurrence5A3Square.coeff 46 =
      ((2090826524490340013960495445296378015746008038519115952284315580905569 * 10 ^ 70 +
        9228158794227619971850004686335431016368681698674038697170592641952849) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_47 :
    recurrence5A3Square.coeff 47 =
      -(((2 * 10 ^ 70 +
        7572449620992398805741267980062120956041005553218725095518557862311559) * 10 ^ 70 +
        7792463268582591114986893866568148425818277698858617875683642233469954) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_48 :
    recurrence5A3Square.coeff 48 =
      (((14 * 10 ^ 70 +
        3784771811508592298098254933128141113978125070243964107176213431383061) * 10 ^ 70 +
        4479061669138887364092372650501874937609763792343826977856687940235486) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_49 :
    recurrence5A3Square.coeff 49 =
      (((622 * 10 ^ 70 +
        3874760536547307444797058436322702309425705216895687675645978213219997) * 10 ^ 70 +
        7913727701046530720320232991571792756664052302149926688713596783251562) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_50 :
    recurrence5A3Square.coeff 50 =
      -(((28782 * 10 ^ 70 +
        9003437708774289525780717417196259433628461878097893682367201375772841) * 10 ^ 70 +
        6259378180893912922254460132347081996166184550550779475900315123574149) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_51 :
    recurrence5A3Square.coeff 51 =
      (((798438 * 10 ^ 70 +
        5119441862903790126577137999366606793447134134294724349026246780695537) * 10 ^ 70 +
        2425252691740575175311241441333642128568747616801022385798271158344088) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_52 :
    recurrence5A3Square.coeff 52 =
      -(((17588091 * 10 ^ 70 +
        6494441672122902186365614542897059593199446906692466583503729467744936) * 10 ^ 70 +
        6916607759758144522258385038215127163147978589033570972110502010030872) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_53 :
    recurrence5A3Square.coeff 53 =
      (((327479859 * 10 ^ 70 +
        5677264132291219703368003864501900810704960337885542762439646045235021) * 10 ^ 70 +
        8719978582217816763813896545534603104016105540061891775341395890829712) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_54 :
    recurrence5A3Square.coeff 54 =
      -(((5200936968 * 10 ^ 70 +
        1128014051954333922456073992412716448166983603627035419068196651639400) * 10 ^ 70 +
        2051469038037532879920882449278843523983597995012989555717046131829122) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_55 :
    recurrence5A3Square.coeff 55 =
      (((68224921058 * 10 ^ 70 +
        1818782384152844731303679930818342319029890268730740517192537555437383) * 10 ^ 70 +
        0185830980835822694775882941840727929902808623079765694499886202968908) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_56 :
    recurrence5A3Square.coeff 56 =
      -(((644167376017 * 10 ^ 70 +
        5193824744617356420271174273377115407556300701709785617564816807740698) * 10 ^ 70 +
        0515707852177017748980989527803729231042541013547449201192963769652560) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_57 :
    recurrence5A3Square.coeff 57 =
      (((975816666110 * 10 ^ 70 +
        5392929564111298419707984164677209237089720344080374302340736656311773) * 10 ^ 70 +
        4855440976339857083581322024348148652239104247785058884755759530355836) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_58 :
    recurrence5A3Square.coeff 58 =
      (((142440259449104 * 10 ^ 70 +
        7868288399649617924938472747669511166447641412751210915722282117907506) * 10 ^ 70 +
        2102685856980623284317757332908912529898925985236376125524661704288581) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_59 :
    recurrence5A3Square.coeff 59 =
      -(((4524778189895068 * 10 ^ 70 +
        0333767163898401978004488902282283119827617271981974631782066076497414) * 10 ^ 70 +
        9472606956248383889841745353592112741809668485137043614713776690235674) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_60 :
    recurrence5A3Square.coeff 60 =
      (((98600111483128853 * 10 ^ 70 +
        1471125153983176277784629494728241361543463954030924830166480108047587) * 10 ^ 70 +
        2295810853996328070259717360496631467757075557990857383582493523278047) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_61 :
    recurrence5A3Square.coeff 61 =
      -(((1799615918029250337 * 10 ^ 70 +
        6637762707509171157687998503809297250723164931989972821898033640891751) * 10 ^ 70 +
        9419088755357423047466648863294920145349477298744721685627254905123856) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_62 :
    recurrence5A3Square.coeff 62 =
      (((29226786096785135326 * 10 ^ 70 +
        6598632219677595146567094347276813802496664848861998746165974502262480) * 10 ^ 70 +
        7155440812012365503582868906566137186869715447395982182593363595593867) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_63 :
    recurrence5A3Square.coeff 63 =
      -(((433993071746667821340 * 10 ^ 70 +
        6695904949060623122947028358519714978469873706877080493183747333818445) * 10 ^ 70 +
        6593067018365465370464759684783831366090306418658387005585468350789754) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_64 :
    recurrence5A3Square.coeff 64 =
      (((5980818577766308123737 * 10 ^ 70 +
        9292775839717814710526336710310899861589751773418497267629399512036540) * 10 ^ 70 +
        9922388126752812057836898270054061007630494074687274738386757446346193) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_65 :
    recurrence5A3Square.coeff 65 =
      -(((77204914074522710761846 * 10 ^ 70 +
        7566740003071471723646733489261655480757138842502592417182156540750971) * 10 ^ 70 +
        6690713369638020217595157690193867805948627167061695218774461223450660) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_66 :
    recurrence5A3Square.coeff 66 =
      (((939451914720523164546713 * 10 ^ 70 +
        4834515287507003873280227691574213174438227228110034260047962656489791) * 10 ^ 70 +
        5450198905685975831587661067920259493411539411779210721675866784792269) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_67 :
    recurrence5A3Square.coeff 67 =
      -(((10825190616939704997447355 * 10 ^ 70 +
        8211179006893203856342581955328764598527985091313486445381554470094062) * 10 ^ 70 +
        6214993600708324796821844815826433071961133232933447659344114910505604) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_68 :
    recurrence5A3Square.coeff 68 =
      (((118533709488669808349652447 * 10 ^ 70 +
        0499472392943932522872702693471261423005140852865127914981644343275112) * 10 ^ 70 +
        7711635852661516090290240932307215259562371212857638431476076237491697) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_69 :
    recurrence5A3Square.coeff 69 =
      -(((1236783883198566475426153712 * 10 ^ 70 +
        3060258314537551798177648041400944758988323387561644132363132794051120) * 10 ^ 70 +
        7226908589573750745776275185606369335713116178542094673802444002754702) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_70 :
    recurrence5A3Square.coeff 70 =
      (((12324616775014453059658391841 * 10 ^ 70 +
        0109640590312846582141519131056648830260188232206081568284356824419590) * 10 ^ 70 +
        9752187882985703294528994392473248359366958159916182289603603216548308) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_71 :
    recurrence5A3Square.coeff 71 =
      -(((117518149462740668527966334030 * 10 ^ 70 +
        8644798158954764064494547903605507601028460245966919156001841665854382) * 10 ^ 70 +
        9720635214980388580826371572159082903313818990705146047568318795941016) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_72 :
    recurrence5A3Square.coeff 72 =
      (((1073976470745713767517014733895 * 10 ^ 70 +
        6537396547155318159202252965631537977745619801461019078847409034135444) * 10 ^ 70 +
        1627976035860434396553520614418769741861482368792901547448579916282963) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_73 :
    recurrence5A3Square.coeff 73 =
      -(((9420170553458137521542643077315 * 10 ^ 70 +
        1159578646732249376791986830386620796270297390581005142219475782244716) * 10 ^ 70 +
        7734824376684834673531029047846591697181927125929205502037463975674160) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_74 :
    recurrence5A3Square.coeff 74 =
      (((79403855380629573690349110019263 * 10 ^ 70 +
        3685607299199232507765489880107204463422803450753683556909660670886263) * 10 ^ 70 +
        6137978215745583985631597541060069518948951404259125783984462164218564) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_75 :
    recurrence5A3Square.coeff 75 =
      -(((643918094023282498155839848433966 * 10 ^ 70 +
        8703633217394536472061228110684214670839304442644609365515740950972168) * 10 ^ 70 +
        2721329106442750182927801943030532268283826407893535986191050754707668) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_76 :
    recurrence5A3Square.coeff 76 =
      (((5028823145706774086805009233585213 * 10 ^ 70 +
        6433613085876441128904193414900926982248711344649669425983429644150511) * 10 ^ 70 +
        2090676790787952503253865677862911779069311775822256444167084339672574) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_77 :
    recurrence5A3Square.coeff 77 =
      -(((37857347169172669406882482515506731 * 10 ^ 70 +
        4388726581991606403994477954083118172326179114725723423339869548663565) * 10 ^ 70 +
        4615333540318785386576873696726255882934502608131653331994532915360306) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_78 :
    recurrence5A3Square.coeff 78 =
      (((274947886176762820381285841479499957 * 10 ^ 70 +
        3865301967018559564073723497945672053107750458565466738378339606263772) * 10 ^ 70 +
        9667094442543903359838842156400218303856207193967654746438706004833300) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_79 :
    recurrence5A3Square.coeff 79 =
      -(((1927999523016928427581929226143956845 * 10 ^ 70 +
        8816621773633776955624063705238888590393608882513685298045523317812505) * 10 ^ 70 +
        0188069623676898446479847740542975242732195900317594412969511218650088) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_80 :
    recurrence5A3Square.coeff 80 =
      (((13062764097208551746853395050264234350 * 10 ^ 70 +
        8871632529578972211133928717396167454567939641239690007474930043966493) * 10 ^ 70 +
        7360200751566980854305243055761902548432658140994230481507533467653522) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_81 :
    recurrence5A3Square.coeff 81 =
      -(((85571377401899485845534406150698980948 * 10 ^ 70 +
        1395865576131313624267599542668080904049553697398520938901896905595348) * 10 ^ 70 +
        1852982632731724357160093193536342972667845949498501290652065558771734) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_82 :
    recurrence5A3Square.coeff 82 =
      (((542327576584186814737309305524569304954 * 10 ^ 70 +
        0698693912005233427221370489213957187678694333988286042060358627941090) * 10 ^ 70 +
        9489397233689123817264556698289201942701245199067071537037701713289355) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_83 :
    recurrence5A3Square.coeff 83 =
      -(((3327299058362642892536710153236172786187 * 10 ^ 70 +
        2226706509250001996661183063408368354992029039162212587152358551981022) * 10 ^ 70 +
        1873870230048963288345612819287219604946238347292543203310822361558568) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_84 :
    recurrence5A3Square.coeff 84 =
      (((19772459902080243603177205932199551155847 * 10 ^ 70 +
        6336244526579378741154528894694529668947378956362379182876426300119056) * 10 ^ 70 +
        4323008720568493605866802666314735410914142573992961126834115580494444) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_85 :
    recurrence5A3Square.coeff 85 =
      -(((113866482153954838984673694957877119654173 * 10 ^ 70 +
        1502616598896440401560430917597828378837508699713273196978694506701633) * 10 ^ 70 +
        1559240276684061309495147296277810667567243164047503889712148750398604) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_86 :
    recurrence5A3Square.coeff 86 =
      (((635787706957963195244847539490817137894928 * 10 ^ 70 +
        6387847890637164610748256879812191796473170318692618921251959293853725) * 10 ^ 70 +
        7263005456716951081182387575445079019140082376707334950763617563206775) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_87 :
    recurrence5A3Square.coeff 87 =
      -(((3443595677585662928971715051826476022578928 * 10 ^ 70 +
        2982919053131278840503666579472600367611139931999064450733286896521354) * 10 ^ 70 +
        4553761137177880013547064228803510775720071389091706509891868470694450) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_88 :
    recurrence5A3Square.coeff 88 =
      (((18100381990765664787367057918050935105425019 * 10 ^ 70 +
        0947789006651775955224746932667740080139136751021977909008701847094053) * 10 ^ 70 +
        9962051052752567888373760443474236734899841576104083741282494289324129) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_89 :
    recurrence5A3Square.coeff 89 =
      -(((92367752935442866396609530301228298362998651 * 10 ^ 70 +
        6025321433719699700327297578688613454445311237961758893210346642929858) * 10 ^ 70 +
        7956936933951820975167348960965538174880941425315892143074448000228250) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_90 :
    recurrence5A3Square.coeff 90 =
      (((457806519183626738408938688562838085347895753 * 10 ^ 70 +
        5362783499739549714712136943378022231917158272362124832298029290803783) * 10 ^ 70 +
        5470418908918067384510493329323799282772775700102821330983999547743889) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_91 :
    recurrence5A3Square.coeff 91 =
      -(((2204628578028991654002262591059919288247262362 * 10 ^ 70 +
        3195856080369869064148670370423734163693235636587064062014067723591830) * 10 ^ 70 +
        5277549535883856549035105296497859346757953352707403073669482706989146) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_92 :
    recurrence5A3Square.coeff 92 =
      (((10318942753419855700588519582831043173814225768 * 10 ^ 70 +
        9629866606457071811483490536605549051905316698275225772810269397402283) * 10 ^ 70 +
        1340567092585591059249726810102350630770934477962151392809917574021625) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_93 :
    recurrence5A3Square.coeff 93 =
      -(((46959962126852759729356954327744168782915244504 * 10 ^ 70 +
        5606214595230155805949010505151851154553648006606074106466858625527035) * 10 ^ 70 +
        3077240305775705761195539667976655460220992504551493440849155882044892) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_94 :
    recurrence5A3Square.coeff 94 =
      (((207850909640583460205928355907956912457396209518 * 10 ^ 70 +
        9499471421216904749596476681198345653058793414740580216079151995228510) * 10 ^ 70 +
        5859413480374580324877194745141087976073461623186918168328631456146326) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_95 :
    recurrence5A3Square.coeff 95 =
      -(((895033924605611575721077205407008485052290869589 * 10 ^ 70 +
        7973629344439624202817273637319831139290594911431041540531355648859840) * 10 ^ 70 +
        5812403667930276471440051651699372042747219572050669657741580001412614) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_96 :
    recurrence5A3Square.coeff 96 =
      (((3750726016612099671120043584572220071840959498765 * 10 ^ 70 +
        0893066291316169359994107281752349921607769935243356771598467090418108) * 10 ^ 70 +
        2762588132811719307020899284002397573153199085067515938345374606611020) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_97 :
    recurrence5A3Square.coeff 97 =
      -(((15300226888036302197706370099693500426900610128474 * 10 ^ 70 +
        0534085847952808091122805885766919282298366547831709076394479710503637) * 10 ^ 70 +
        6571013163716057354746893424113331048954673646414377334483325362076198) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_98 :
    recurrence5A3Square.coeff 98 =
      (((60771408805166216512274812615945960814251061148003 * 10 ^ 70 +
        5504057762802868615781813644650884718503765897059340511620801844917421) * 10 ^ 70 +
        0524444704702715243701594705205520513043852217147158913478427430094303) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_99 :
    recurrence5A3Square.coeff 99 =
      -(((235085554622581685562352460911796427213040461517877 * 10 ^ 70 +
        5820760466999613935473605963616491083136402985430837297660201242722835) * 10 ^ 70 +
        9963919824938196863530573654258064419148798060919628613244944242883126) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_100 :
    recurrence5A3Square.coeff 100 =
      (((885887218756959391447407091301005084311979404307172 * 10 ^ 70 +
        7659733528952159901060635394219840137492481503002961247685264877405142) * 10 ^ 70 +
        5641506619614754762183241227499637192983912882926464715578335505397654) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_101 :
    recurrence5A3Square.coeff 101 =
      -(((3252759925004934940090285398699491582023776306426784 * 10 ^ 70 +
        9594791864269207102301067068799371168026237453558111565326187955541611) * 10 ^ 70 +
        3603346519881053667572705958937987254538444765460396752439406606773908) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_102 :
    recurrence5A3Square.coeff 102 =
      (((11639563781897580721363332187997374895850480446481835 * 10 ^ 70 +
        7891222468680511180683780427244183818790320668327846702449369545116105) * 10 ^ 70 +
        4227798584326099756376952295304222148486212401502067378218702651482986) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_103 :
    recurrence5A3Square.coeff 103 =
      -(((40599208646965873394247136684361658632760155174023947 * 10 ^ 70 +
        1043809818607322531037548332446374401105836714794912661025154043535730) * 10 ^ 70 +
        5772712148403344657883397240588483107653073712629540159129394702035240) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_104 :
    recurrence5A3Square.coeff 104 =
      (((138062223284583280219717935169449580474268931504703849 * 10 ^ 70 +
        3974978147387189445292065412732885151558427609908346237075813631102585) * 10 ^ 70 +
        1097178661363146078053441574498493387552331459233691400812781509192267) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_105 :
    recurrence5A3Square.coeff 105 =
      -(((457808906477719544127630426669468391967715145119034297 * 10 ^ 70 +
        1823224549727340577469378293720447451421017424592429028678298038197265) * 10 ^ 70 +
        8005796118799348259974579720059237436101037661110760888133397603379226) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_106 :
    recurrence5A3Square.coeff 106 =
      (((1480528938919711688035013632578713703614718248810984379 * 10 ^ 70 +
        9521956479925824204798306891019541047242066906015366545965871798639882) * 10 ^ 70 +
        3490425900932523742614572517905276600941386103095407668873525361121910) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_107 :
    recurrence5A3Square.coeff 107 =
      -(((4670246191100687692108181809857095463212609653833355526 * 10 ^ 70 +
        5332159279896051795738918720670939337895589617307216132135385572031183) * 10 ^ 70 +
        5990144661263794290829786750929269336660683950047073955993452594364170) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_108 :
    recurrence5A3Square.coeff 108 =
      (((14371948122510060683347845271140109275172159002275051667 * 10 ^ 70 +
        7407470968681426220499547231297557676549683365499473391757116410818659) * 10 ^ 70 +
        4346298768362300732592110920095023994642128542283982085590117950430225) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_109 :
    recurrence5A3Square.coeff 109 =
      -(((43152232583116293205435696660613217052575140696056416044 * 10 ^ 70 +
        3456986948818826220208688942862882036856741905300451567729391859509649) * 10 ^ 70 +
        8172303281471487953942221923252823462434683076125120642975124590141848) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_110 :
    recurrence5A3Square.coeff 110 =
      (((126432156100739535271304464909839781935525646121318721431 * 10 ^ 70 +
        3659252686117285539168072656851828607629205227411870974020691499985929) * 10 ^ 70 +
        8898426086026408063258450160967284293555663867256084556453757082152586) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_111 :
    recurrence5A3Square.coeff 111 =
      -(((361517700312779795700715053207872604024457189016816215573 * 10 ^ 70 +
        5166455618330460517847797741605982889188580270442640806938723804287949) * 10 ^ 70 +
        2405238453734916010982409950431044185596144688580519615685431394369998) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_112 :
    recurrence5A3Square.coeff 112 =
      (((1008943280170373215600251090206979530680179923128411877190 * 10 ^ 70 +
        5814404049255936669040567215151647332335197329604872157135924034364895) * 10 ^ 70 +
        3292249165026485362688052198823008929955147169475804717071933040295702) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_113 :
    recurrence5A3Square.coeff 113 =
      -(((2748608728716449547945655963297806016216702969377790030426 * 10 ^ 70 +
        3699954939913370409493265214994111241914336174352519389269399552067928) * 10 ^ 70 +
        7914400404338335656596991741869562375344463341787586266753377168231586) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_114 :
    recurrence5A3Square.coeff 114 =
      (((7309848263007492082929239796027167407535447320210629990208 * 10 ^ 70 +
        6027984279218925360253224152090475676080058390696772974011739977521704) * 10 ^ 70 +
        5404146151534014818390306538312255036728745675900342111968500921975798) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_115 :
    recurrence5A3Square.coeff 115 =
      -(((18979723954188548646709832426851990974347132569269407510330 * 10 ^ 70 +
        1891860153148404594618801881015583555673728712260810604533440566071655) * 10 ^ 70 +
        5971723606987576815880426163951412287367249951951229674905214061998536) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_116 :
    recurrence5A3Square.coeff 116 =
      (((48116153309017656246279198657315239364214067382612953296259 * 10 ^ 70 +
        6219441911146573423138315304044027623277875106755368256409009682517242) * 10 ^ 70 +
        3628448726641245956296818849437933059455526599174838289340970307111317) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_117 :
    recurrence5A3Square.coeff 117 =
      -(((119108122134068516403509272875981518525209353831613677903299 * 10 ^ 70 +
        4682291341548528847146534267269572300119899564145621301484175800785178) * 10 ^ 70 +
        3252327029774976487494113990724249719140681744402108350572667162223990) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_118 :
    recurrence5A3Square.coeff 118 =
      (((287917411110679172372693369881021669120046787746123812912451 * 10 ^ 70 +
        7873946422112662216271464119015877550759857411219497314758141611289322) * 10 ^ 70 +
        6961674397618078218641924332477365046577727965394219318841002581297716) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_119 :
    recurrence5A3Square.coeff 119 =
      -(((679663215910132816679444181642853359860192085004833546595861 * 10 ^ 70 +
        8591450172129414663986421477154114309377460307347601731456987142868293) * 10 ^ 70 +
        1745305489482532097613185163337006653178766930767365497176962964284288) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_120 :
    recurrence5A3Square.coeff 120 =
      (((1566890650194337156165663930278300809544290076787556466365038 * 10 ^ 70 +
        9324666366263273052921126672318608478879061877390949752308492601302377) * 10 ^ 70 +
        1769637989119678987939887915186473114288127120737479362081309256562881) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_121 :
    recurrence5A3Square.coeff 121 =
      -(((3527922523124494704189950826246507234688933475325726353897979 * 10 ^ 70 +
        6920248823834288502236333242948904358079757899000650264484862099278036) * 10 ^ 70 +
        2863871434626560003350769638655077375906715214459978713754087560505370) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_122 :
    recurrence5A3Square.coeff 122 =
      (((7757961746211855508071212970414527653197186105763884319874450 * 10 ^ 70 +
        9922131246092210304552275869484478034189581459317899363639707947135700) * 10 ^ 70 +
        6936011793849661368303512840513417812945697374991475218444345462096890) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_123 :
    recurrence5A3Square.coeff 123 =
      -(((16662251183346368298848434464250054431031141509242976157377419 * 10 ^ 70 +
        0302530883468184068110197041151313698611150883728490749772323761658650) * 10 ^ 70 +
        4300882709195645700823986693510051023571160508225618013724678823665878) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_124 :
    recurrence5A3Square.coeff 124 =
      (((34952853745634759858689871378650321929016978374916016847879425 * 10 ^ 70 +
        8907927787321991851881832829304015488076746109471683041945601689455441) * 10 ^ 70 +
        1784196368294529650556321665410282991523408282641162792070558173931948) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_125 :
    recurrence5A3Square.coeff 125 =
      -(((71613699368685513656207672642275756369450173565947176832871348 * 10 ^ 70 +
        7494236858966479125335689855330647371484318327732084994526655691594876) * 10 ^ 70 +
        7492932632988990431277485890592784631898994751259923686508838591636842) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_126 :
    recurrence5A3Square.coeff 126 =
      (((143308384948059531188308762232477042553259716905696895298104378 * 10 ^ 70 +
        8979483628999105650244971886643240932570649216769616740692234292856953) * 10 ^ 70 +
        8230492346099345231160015228183595827517098515110765673326491278057266) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_127 :
    recurrence5A3Square.coeff 127 =
      -(((280093053337420085442633672740659562682050788760788191182972846 * 10 ^ 70 +
        8587064373614539193384165618417170096707252054384301010705143375770313) * 10 ^ 70 +
        1890427124482392872363628731142729192660964432419862515101848215103452) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_128 :
    recurrence5A3Square.coeff 128 =
      (((534659100279929937592473812775726945181974747070420740996117377 * 10 ^ 70 +
        6861030391162243976305449136606024913103386692703285935840672979216488) * 10 ^ 70 +
        1299308780469331173283923323663039845938279050958193917425337098399617) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_129 :
    recurrence5A3Square.coeff 129 =
      -(((996733870989543635284145135357710128253824767567210668626755779 * 10 ^ 70 +
        4168036005507334405414860551250534900404865000480083169426957503938744) * 10 ^ 70 +
        7954994228637902345029838838039612165908052300467063722906788632791046) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_130 :
    recurrence5A3Square.coeff 130 =
      (((1814627681469202915661427840121524406465666150955101285199956998 * 10 ^ 70 +
        8780865859265260125088763154580759139913080174100654679465302468642071) * 10 ^ 70 +
        9478933204900502162335888666444183536494232361236453720924780489956831) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_131 :
    recurrence5A3Square.coeff 131 =
      -(((3226075719531264362477656513071540383370322115023516797655934705 * 10 ^ 70 +
        8656479269749818954705114097410057083660637757681611713702326052276452) * 10 ^ 70 +
        3685618589377721707763886904526560501626392144627027605536347070667840) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_132 :
    recurrence5A3Square.coeff 132 =
      (((5600239250233129793263870706084489067122184398305354314276888904 * 10 ^ 70 +
        9517474624928006465393630784215794343632833772956403843833965060180137) * 10 ^ 70 +
        8810465527168465679354132644320858693230908908636022875991504325342149) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_133 :
    recurrence5A3Square.coeff 133 =
      -(((9491674690120239620648737422326972585437524162814925220762751698 * 10 ^ 70 +
        0832844371771010509783390551979229607776943365990080069750886300831899) * 10 ^ 70 +
        6369301357618252506721190855628886622691490247693465837678803083328598) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_134 :
    recurrence5A3Square.coeff 134 =
      (((15704883035419650130808683478309013285722578727120188820222400908 * 10 ^ 70 +
        3045052874215611973178251196899498396781591398286428225467528678248752) * 10 ^ 70 +
        7118280928596554272787228279428750417736016764719072019379605550352785) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_135 :
    recurrence5A3Square.coeff 135 =
      -(((25364402188409263545894209919624985355884226088457760939397288824 * 10 ^ 70 +
        5673074312690078500644222547060586173008623641065658685713879296597313) * 10 ^ 70 +
        7006823113064350748753335366487275904938979420524493437002209418429844) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_136 :
    recurrence5A3Square.coeff 136 =
      (((39980200334826957355581637319054816772324516005666459038103387139 * 10 ^ 70 +
        5955358192154969254141923189434989868459596547248091192289888634607941) * 10 ^ 70 +
        7562730309101816758324391398052827448903012619128032714915353053211344) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_137 :
    recurrence5A3Square.coeff 137 =
      -(((61491690491918186705438927429336180847907054017892519558881322091 * 10 ^ 70 +
        9481668698166660844303519300726222860258715337330087662616207686284878) * 10 ^ 70 +
        5802820836414917926492827306469832904583569192572965982850142924907574) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_138 :
    recurrence5A3Square.coeff 138 =
      (((92266971410337212670405083055956880650075708075756735734828496802 * 10 ^ 70 +
        7506045028448793236837858686782750983509705398666320614475390165437767) * 10 ^ 70 +
        5053923461091846610117463335621713248688075924586295419300647733446450) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_139 :
    recurrence5A3Square.coeff 139 =
      -(((135028640231729459684015562453849868779891478667335061200896659300 * 10 ^ 70 +
        9980539282031739265786666426930303584285563059094613016944605439573573) * 10 ^ 70 +
        0508831801800721419410593896630735545714432885241038044297274828936756) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_140 :
    recurrence5A3Square.coeff 140 =
      (((192676178647735967474305884341069328210014045297455234135054037070 * 10 ^ 70 +
        7022149447717225417056133678926033965299720281565834316947987511825731) * 10 ^ 70 +
        4835189549521200191865698887994324506933369861813323145723933596323802) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_141 :
    recurrence5A3Square.coeff 141 =
      -(((267980332579399663891702837384129251567914192710700874278432831046 * 10 ^ 70 +
        2740971251271040438539719961736196043763566902480018029083314261126299) * 10 ^ 70 +
        7351499929409932528843350364638863421712787937486523531562584747793494) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_142 :
    recurrence5A3Square.coeff 142 =
      (((363139610165395166381448529151691717800906125170113887787844990623 * 10 ^ 70 +
        4116147733217912133600018290261648460609612192282470147002960431587042) * 10 ^ 70 +
        8893818725349568432216022193788311233057875359885942774688206020944885) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_143 :
    recurrence5A3Square.coeff 143 =
      -(((479214192425595181844917955505815974752267414294575876403993542336 * 10 ^ 70 +
        0860330538597800727488169551530082260175827767027390619973885098669292) * 10 ^ 70 +
        8495581696687002381149079154722745538001633378397289149996681166255236) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_144 :
    recurrence5A3Square.coeff 144 =
      (((615486872836267079704770142427501733037186014445125364698524257768 * 10 ^ 70 +
        1565872550163480757673881522380711999868515444604265836721762124209614) * 10 ^ 70 +
        6342916024594194584923106937071492246770078619164764255806907177074141) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_145 :
    recurrence5A3Square.coeff 145 =
      -(((768839412145683769807045079102633983015424452636797207233449240447 * 10 ^ 70 +
        8179679100778336591319968808681910465664996298288775343724169059819299) * 10 ^ 70 +
        1549747213526733981063068146196570624723420645184561973565640775590566) : ℚ) := by
  unfold recurrence5A3Square
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

theorem recurrence5A3Square_coeff_146 :
    recurrence5A3Square.coeff 146 =
      (((933267626111969692645209949164669008385701624409162590173014271049 * 10 ^ 70 +
        0072495117502431052629870730368450882397908488599586567328237144647453) * 10 ^ 70 +
        9466715493864678523579110441025978686911317918581748611757708716866969) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5A3Square_coeff_147 :
    recurrence5A3Square.coeff 147 =
      -(((1099678690833265995612966964004727628243971182274957508836703578444 * 10 ^ 70 +
        0968340682297204636826686107527809945266569169143083323221163770232603) * 10 ^ 70 +
        4965218125142684708719133133009169990097707212033761052514508554948126) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 20 = 20 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5A3Square_coeff_148 :
    recurrence5A3Square.coeff 148 =
      (((1256108258128035242621126915357590650496180969323522761893945754979 * 10 ^ 70 +
        1832480589679624536660511507756749773135664073085776887396702947028904) * 10 ^ 70 +
        0977653307266375625310654738367489344430710342562149214142941514374495) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5A3Square_coeff_149 :
    recurrence5A3Square.coeff 149 =
      -(((1388454716146650427776327758547593306828686780614612060318079346146 * 10 ^ 70 +
        7142444824851216831811192003262975779236537929380842657777204292353318) * 10 ^ 70 +
        2554890548364062617664603691839012673610993366095768942810433065989956) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 22 = 22 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5A3Square_coeff_150 :
    recurrence5A3Square.coeff 150 =
      (((1481751683869969722640382649129139728846740292896132102083173261537 * 10 ^ 70 +
        4581262906628586976434831554502980904903468407698601172195366967441768) * 10 ^ 70 +
        8894101204391276340731390256633699585448025675178256394744528998403234) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5A3Square_coeff_151 :
    recurrence5A3Square.coeff 151 =
      -(((1521895496481648718542346746453654776872696379523637087304874640358 * 10 ^ 70 +
        0711111843943532808010261975192062194843230183123973282912976031879641) * 10 ^ 70 +
        4143893625781365059012167797524392264269288838496941563094065549225854) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 24 = 24 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5A3Square_coeff_152 :
    recurrence5A3Square.coeff 152 =
      (((1497630156266997820878783443673123921948095938842626773461202095495 * 10 ^ 70 +
        2573876404061973298795382813495694572875880041919976258730542130850028) * 10 ^ 70 +
        5974748757564090418259536381954506401562711378031254855148657118288732) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5A3Square_coeff_153 :
    recurrence5A3Square.coeff 153 =
      -(((1402493969127510626858012445302702633773330743365327624398094182291 * 10 ^ 70 +
        9526052374607459836250574703888169276923559591331634109473604323927896) * 10 ^ 70 +
        8882786786791090944593836787393776486282313531976379690830722748103576) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 26 = 26 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5A3Square_coeff_154 :
    recurrence5A3Square.coeff 154 =
      (((1236378104371150462887449623214714883675711967671418948558155549007 * 10 ^ 70 +
        8445881621663810154066741602146754547703994097110408622521621661958657) * 10 ^ 70 +
        7457308537875954103333790448106659671394594414101492413842596636782021) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5A3Square_coeff_155 :
    recurrence5A3Square.coeff 155 =
      -(((1006360376810882492079681159456241302294065825364196178706682070273 * 10 ^ 70 +
        3507947351137837074774223641333147689292616328104777675578209802352273) * 10 ^ 70 +
        2084264132182283877503479301593251268135872094683612463332789568893496) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 28 = 28 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5A3Square_coeff_156 :
    recurrence5A3Square.coeff 156 =
      (((726567135405850897862001792114410713323513006759163707244894790424 * 10 ^ 70 +
        7576189545026045025526591099339360364175893057765849331801157064515448) * 10 ^ 70 +
        7840801199018409642647822852628606174679670913269674635277368412135946) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 29 = 29 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5A3Square_coeff_157 :
    recurrence5A3Square.coeff 157 =
      -(((416973139222589725788707450398728371172366660252444911065154903519 * 10 ^ 70 +
        5625104272904119498941819092633875969700328111671041793750616789314120) * 10 ^ 70 +
        7167959876717399319351218525272249739996000795690350075460576886428994) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 30 = 30 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5A3Square_coeff_158 :
    recurrence5A3Square.coeff 158 =
      (((101245473449333062911498652699106612526293358935604980916205629989 * 10 ^ 70 +
        3287519468162456245283445347860882923706884988240410069946869490704132) * 10 ^ 70 +
        6751883580677840908336389864495247370193984419651699394249960190882137) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 31 = 31 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5A3Square_coeff_159 :
    recurrence5A3Square.coeff 159 =
      (((196069220101287954880260078334796014939293381096260162068168634804 * 10 ^ 70 +
        9241629809551428552624955555562470025187659445251793485863067759105993) * 10 ^ 70 +
        2333145180644191182748863922176444078245437808879234890922897358552420) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5A3Square_coeff_160 :
    recurrence5A3Square.coeff 160 =
      -(((452570519694790753668104508363162201456516786621410943687033686377 * 10 ^ 70 +
        7506657887810563633801804200943749806372273937449988384756480107686868) * 10 ^ 70 +
        0840265504689033680564703143435437514960559926769406183572555519683202) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 33 = 32 +
      1 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 1 = 1 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5A3Square_coeff_161 :
    recurrence5A3Square.coeff 161 =
      (((650740952662830912429751191836100930711649382743870237161179842500 * 10 ^ 70 +
        8752716870257719460396898863785468637112351117127116477807949812657629) * 10 ^ 70 +
        1624818784112829320146917642156349887838668030664075756008746266042312) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 34 = 32 +
      2 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 2 = 2 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5A3Square_coeff_162 :
    recurrence5A3Square.coeff 162 =
      -(((779936907661086548885091540691512986782323508738621994484604633814 * 10 ^ 70 +
        8830190405250418636386140484862363278526593625508077297046100600744330) * 10 ^ 70 +
        1091219794624112385457483621197766624176460387819729571780615787176455) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5A3Square_coeff_163 :
    recurrence5A3Square.coeff 163 =
      (((837318115446979635495087694903284866101427140478437938463293417537 * 10 ^ 70 +
        2712858652617545113402551206760491108443038654489997639747755827677143) * 10 ^ 70 +
        6167806090240560858299282513939504919804964531592790073412518566328190) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 36 = 32 +
      4 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5A3Square_coeff_164 :
    recurrence5A3Square.coeff 164 =
      -(((827605214713464825219866873697743967097915724868492662002340922419 * 10 ^ 70 +
        6592097480285415548893601645100117393217943132237794333578769586145835) * 10 ^ 70 +
        5827346839643299711989434168934988016398276380936740703796002986198819) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 37 = 32 +
      5 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 5 = 5 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_165_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (165 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_165_suffix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (165 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_165 :
    recurrence5A3Square.coeff 165 =
      (((761776395750897860001676882701927981774909967221639014797457011014 * 10 ^ 70 +
        8197688070159743007640686975850722281612998495843481784853268571405582) * 10 ^ 70 +
        9200629076069655035045712423752922299161705140176971950981110779325986) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 37 = 32 +
      5 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 5 = 4 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_165_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_165_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_166_prefix_zero :
    (∑ x ∈ Finset.range 2,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (166 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (166 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_166_suffix_zero :
    (∑ x ∈ Finset.range 2,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (166 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_166 :
    recurrence5A3Square.coeff 166 =
      -(((655001459518548318380337527108124069506388780212302546174053126637 * 10 ^ 70 +
        2033493412034869329046767160396898170359839458220235669237265778928487) * 10 ^ 70 +
        0990724237116850289130006510846164371667270343223991895445106089932607) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 37 = 32 +
      5 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 5 = 3 +
      2 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_166_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_166_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_167_prefix_zero :
    (∑ x ∈ Finset.range 3,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (167 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (167 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_167_suffix_zero :
    (∑ x ∈ Finset.range 3,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (167 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_167 :
    recurrence5A3Square.coeff 167 =
      (((524224977263957768957460841823558454489630417630360968767528156878 * 10 ^ 70 +
        0057459879090861845110785187139172651213693435546200677823586905261657) * 10 ^ 70 +
        4197850333885647022929090825816669106875160900162014331207827640548218) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 37 = 32 +
      5 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 5 = 2 +
      3 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_167_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_167_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_168_prefix_zero :
    (∑ x ∈ Finset.range 4,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (168 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (168 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_168_suffix_zero :
    (∑ x ∈ Finset.range 4,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (168 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_168 :
    recurrence5A3Square.coeff 168 =
      -(((385830243214283869097874490813317374360436565447461371267921207637 * 10 ^ 70 +
        4267158747196068785727681183062183804999481806058965226505129669262741) * 10 ^ 70 +
        1992063223744970347339282156152238003521965313560949459664835940583435) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 37 = 32 +
      5 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 5 = 1 +
      4 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_168_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_168_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_169_prefix_zero :
    (∑ x ∈ Finset.range 5,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (169 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (169 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_169_suffix_zero :
    (∑ x ∈ Finset.range 5,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (169 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_169 :
    recurrence5A3Square.coeff 169 =
      (((253747114393593449536030776044437150893574118724292180234876556467 * 10 ^ 70 +
        7752527768760132640662682663809575446250760174502647867634132191315506) * 10 ^ 70 +
        0627275818872975751136043523459920058646363903898996587371001343372760) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 37 = 32 +
      5 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_169_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_169_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_170_prefix_zero :
    (∑ x ∈ Finset.range 6,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (170 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (170 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_170_suffix_zero :
    (∑ x ∈ Finset.range 6,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (170 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_170 :
    recurrence5A3Square.coeff 170 =
      -(((138235003035896504637634421387034539552754981749327691077872196979 * 10 ^ 70 +
        3162843225189385776035310908316682188518301961431271675181262020307734) * 10 ^ 70 +
        8452741673921032958238765868759081660195691776636215770608770979099137) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 37 = 31 +
      6 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_170_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_170_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_171_prefix_zero :
    (∑ x ∈ Finset.range 7,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (171 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (171 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_171_suffix_zero :
    (∑ x ∈ Finset.range 7,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (171 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_171 :
    recurrence5A3Square.coeff 171 =
      (((45414444956533158455779373736567845608226336209056793012278886942 * 10 ^ 70 +
        9632146029959315114680679517444604917678977877426118513304142852704316) * 10 ^ 70 +
        5227861124245574758038502023845617505954395542301272023543523739028134) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 37 = 30 +
      7 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_171_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_171_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_172_prefix_zero :
    (∑ x ∈ Finset.range 8,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (172 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (172 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_172_suffix_zero :
    (∑ x ∈ Finset.range 8,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (172 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_172 :
    recurrence5A3Square.coeff 172 =
      (((22525141907092053402660785404837884414702147497527944229781793785 * 10 ^ 70 +
        2781251723554891782971941667065372558159640463091428321097514245344798) * 10 ^ 70 +
        5088502037912418898041588740546418888968234756701526725671330262005091) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 37 = 29 +
      8 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_172_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_172_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_173_prefix_zero :
    (∑ x ∈ Finset.range 9,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (173 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (173 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_173_suffix_zero :
    (∑ x ∈ Finset.range 9,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (173 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_173 :
    recurrence5A3Square.coeff 173 =
      -(((66618530425766791120096630457718427015145937217432369863819838718 * 10 ^ 70 +
        0568300084663008477477473782740142429702956664141804932507035729263011) * 10 ^ 70 +
        8287016987060671877834712397837658609497092728773177944333754258094820) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 37 = 28 +
      9 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_173_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_173_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_174_prefix_zero :
    (∑ x ∈ Finset.range 10,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (174 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (174 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_174_suffix_zero :
    (∑ x ∈ Finset.range 10,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (174 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_174 :
    recurrence5A3Square.coeff 174 =
      (((90144666026527989555547934906854821629906272996804774247712167623 * 10 ^ 70 +
        7377597772058183663756238623445306127050336719688241354398404899590317) * 10 ^ 70 +
        9416248525240046521788102760107513287662533128250054818554445442139610) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 37 = 27 +
      10 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_174_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_174_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_175_prefix_zero :
    (∑ x ∈ Finset.range 11,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (175 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (175 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_175_suffix_zero :
    (∑ x ∈ Finset.range 11,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (175 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_175 :
    recurrence5A3Square.coeff 175 =
      -(((97594312156446209732460989547409350471316446003993429131655522930 * 10 ^ 70 +
        8981142330140553183985689988790996516192936106800456577968528967899750) * 10 ^ 70 +
        3422688766371698016709815840315038351680222914821601431695642674504620) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 37 = 26 +
      11 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_175_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_175_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_176_prefix_zero :
    (∑ x ∈ Finset.range 12,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (176 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (176 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_176_suffix_zero :
    (∑ x ∈ Finset.range 12,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (176 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_176 :
    recurrence5A3Square.coeff 176 =
      (((93759782940891402868351736704197845356217844441083034948706090488 * 10 ^ 70 +
        8051900139711289180750271005753135322628529208618899162247437208663651) * 10 ^ 70 +
        8031567490954005926602621140571084329282287679205930833728927155261302) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 37 = 25 +
      12 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_176_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_176_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_177_prefix_zero :
    (∑ x ∈ Finset.range 13,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (177 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (177 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_177_suffix_zero :
    (∑ x ∈ Finset.range 13,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (177 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_177 :
    recurrence5A3Square.coeff 177 =
      -(((83053442329299933801673203942571470787989281113116832495944316625 * 10 ^ 70 +
        8334350170688637862291087110891419166067341792611353068167534880874709) * 10 ^ 70 +
        8835811249583853969454141105501540267518695912076035997721606793564330) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 37 = 24 +
      13 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_177_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_177_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_178_prefix_zero :
    (∑ x ∈ Finset.range 14,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (178 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (178 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_178_suffix_zero :
    (∑ x ∈ Finset.range 14,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (178 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_178 :
    recurrence5A3Square.coeff 178 =
      (((69092074754004621748465050817926119887220607789414352059075923005 * 10 ^ 70 +
        2368994417668275352121844554854229628161654927558325266482513165496862) * 10 ^ 70 +
        7635385671048378620263788784989540224792898139681290424382888503457227) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 37 = 23 +
      14 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_178_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_178_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_179_prefix_zero :
    (∑ x ∈ Finset.range 15,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (179 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (179 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_179_suffix_zero :
    (∑ x ∈ Finset.range 15,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (179 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_179 :
    recurrence5A3Square.coeff 179 =
      -(((54527662505134348048755481403345343475135112273963252246306297071 * 10 ^ 70 +
        5867139428658354816568186691845009164464602107855429120716645338990863) * 10 ^ 70 +
        0841060017061043969902944023637287700582006812569890751776800048224854) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 37 = 22 +
      15 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_179_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_179_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_180_prefix_zero :
    (∑ x ∈ Finset.range 16,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (180 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (180 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_180_suffix_zero :
    (∑ x ∈ Finset.range 16,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (180 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_180 :
    recurrence5A3Square.coeff 180 =
      (((41069334904829665223429420691885354147690383822646332439204146434 * 10 ^ 70 +
        1274583547075494602820521096612911775918549939854693055255903553532871) * 10 ^ 70 +
        7974908353985676960792199046252432258208517452186321151587928736623548) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 37 = 21 +
      16 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_180_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_180_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_181_prefix_zero :
    (∑ x ∈ Finset.range 17,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (181 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (181 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_181_suffix_zero :
    (∑ x ∈ Finset.range 17,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (181 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_181 :
    recurrence5A3Square.coeff 181 =
      -(((29627179825165827780785859958084825598820914877394685035577634931 * 10 ^ 70 +
        1141340996096814057190369508276311840812290425131973919232863150188079) * 10 ^ 70 +
        0203531675740674464201093523288140401920010244632339135525187422967060) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 37 = 20 +
      17 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_181_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_181_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_182_prefix_zero :
    (∑ x ∈ Finset.range 18,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (182 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (182 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_182_suffix_zero :
    (∑ x ∈ Finset.range 18,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (182 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_182 :
    recurrence5A3Square.coeff 182 =
      (((20512082050075401465402704132563630919865096411408404633327304953 * 10 ^ 70 +
        5894315194534747975228346261928155999066676801706866216765034148423815) * 10 ^ 70 +
        2754633670650918571360208115167007003605698661644078046836031472048544) : ℚ) := by
  unfold recurrence5A3Square
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
    rhs
    rw [show 37 = 19 +
      18 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_182_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_182_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_183_prefix_zero :
    (∑ x ∈ Finset.range 19,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (183 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (183 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_183_suffix_zero :
    (∑ x ∈ Finset.range 19,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (183 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_183 :
    recurrence5A3Square.coeff 183 =
      -(((13640151924655458478605124992121883098498735849394152004177450278 * 10 ^ 70 +
        1108969284404221450689836428488261314845148372916771293560357675034849) * 10 ^ 70 +
        4384541785221592780803345029984723074298410898124611286738801400584026) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 18 +
      19 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_183_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_183_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_184_prefix_zero :
    (∑ x ∈ Finset.range 20,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (184 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (184 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_184_suffix_zero :
    (∑ x ∈ Finset.range 20,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (184 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_184 :
    recurrence5A3Square.coeff 184 =
      (((8708899677694449368390884871933188124987861981658393337181060605 * 10 ^ 70 +
        0671706148296579093767836037980950247935637062337371194964556646093085) * 10 ^ 70 +
        2026697372434093491869433423960042365947375907117122480119527763686449) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 17 +
      20 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_184_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_184_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_185_prefix_zero :
    (∑ x ∈ Finset.range 21,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (185 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (185 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_185_suffix_zero :
    (∑ x ∈ Finset.range 21,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (185 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_185 :
    recurrence5A3Square.coeff 185 =
      -(((5329857611244955750094269894261024700221815681923578375374932014 * 10 ^ 70 +
        2445288203463178085755156069027111210561443759377683743548472495428993) * 10 ^ 70 +
        1946982518501859720299883256776095169405118614131255081120456674979630) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 16 +
      21 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_185_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_185_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_186_prefix_zero :
    (∑ x ∈ Finset.range 22,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (186 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (186 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_186_suffix_zero :
    (∑ x ∈ Finset.range 22,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (186 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_186 :
    recurrence5A3Square.coeff 186 =
      (((3115781803338343378749910981530944617448471166692068149122411109 * 10 ^ 70 +
        5542822601127559208601321230759416156987576400403077751850073233040472) * 10 ^ 70 +
        2672809582429015881171832469266087244673885081700007448448922546660769) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 15 +
      22 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_186_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_186_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_187_prefix_zero :
    (∑ x ∈ Finset.range 23,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (187 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (187 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_187_suffix_zero :
    (∑ x ∈ Finset.range 23,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (187 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_187 :
    recurrence5A3Square.coeff 187 =
      -(((1728864879779653182642533572085641520282383296963250946203179442 * 10 ^ 70 +
        1196052238766766462240552552642168425120683034872981813696319288138777) * 10 ^ 70 +
        6185499813309192304744914537940610880819968339474682645488020591615410) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 14 +
      23 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_187_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_187_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_188_prefix_zero :
    (∑ x ∈ Finset.range 24,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (188 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (188 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_188_suffix_zero :
    (∑ x ∈ Finset.range 24,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (188 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_188 :
    recurrence5A3Square.coeff 188 =
      (((900039877845548416690007908005419183714681244503497258028229643 * 10 ^ 70 +
        1163526285230190291330789993758878015690936697130327572284210549262924) * 10 ^ 70 +
        6721404678688055428925964799154507652240406217152833519762210848584983) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 13 +
      24 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_188_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_188_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_189_prefix_zero :
    (∑ x ∈ Finset.range 25,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (189 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (189 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_189_suffix_zero :
    (∑ x ∈ Finset.range 25,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (189 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_189 :
    recurrence5A3Square.coeff 189 =
      -(((429712233199633839991567293363439365139532470445696674062340781 * 10 ^ 70 +
        1266080421415402396014443132396550435974585103110738532959311604829995) * 10 ^ 70 +
        5488963517010354888201163563854527455213849092513384386559782951416072) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 12 +
      25 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_189_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_189_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_190_prefix_zero :
    (∑ x ∈ Finset.range 26,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (190 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (190 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_190_suffix_zero :
    (∑ x ∈ Finset.range 26,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (190 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_190 :
    recurrence5A3Square.coeff 190 =
      (((178554888260308744798605351965166093713191465780846669387654255 * 10 ^ 70 +
        1932855898491804881767894909025224494921709035648160131941557785913763) * 10 ^ 70 +
        3081809341175198990974473162624653973840552685051314099683159627887249) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 11 +
      26 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_190_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_190_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_191_prefix_zero :
    (∑ x ∈ Finset.range 27,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (191 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (191 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_191_suffix_zero :
    (∑ x ∈ Finset.range 27,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (191 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_191 :
    recurrence5A3Square.coeff 191 =
      -(((54550356320818597438313412533021651033068850470973022003055685 * 10 ^ 70 +
        6851165584780857508574054735426056336397454108972425173765766917419896) * 10 ^ 70 +
        2592832681028403285712879691308962779731925453896005595910323154106704) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 10 +
      27 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_191_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_191_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_192_prefix_zero :
    (∑ x ∈ Finset.range 28,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (192 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (192 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_192_suffix_zero :
    (∑ x ∈ Finset.range 28,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (192 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_192 :
    recurrence5A3Square.coeff 192 =
      (((79947986079124818781411508187643733264007354146059326235826 * 10 ^ 70 +
        8788641382508637812167172088113913542853935351261498657428237994829208) * 10 ^ 70 +
        8383355844330055557577817296688410381994863836563461300715694302074870) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 9 +
      28 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_192_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_192_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_193_prefix_zero :
    (∑ x ∈ Finset.range 29,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (193 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (193 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_193_suffix_zero :
    (∑ x ∈ Finset.range 29,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (193 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_193 :
    recurrence5A3Square.coeff 193 =
      (((19033585229871521603635727455854202438437269180620431995229184 * 10 ^ 70 +
        6887226835084185243990397228568769895764039907375549617772294725447126) * 10 ^ 70 +
        7733711428957881454155092267570076416130860253939500444169016806327422) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 8 +
      29 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_193_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_193_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_194_prefix_zero :
    (∑ x ∈ Finset.range 30,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (194 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (194 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_194_suffix_zero :
    (∑ x ∈ Finset.range 30,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (194 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_194 :
    recurrence5A3Square.coeff 194 =
      -(((21908149269648278913052561826394292426415896710593631842298270 * 10 ^ 70 +
        7565396811212562719419877134326117000322586212972673598492327025181976) * 10 ^ 70 +
        9220873766674773731400734255703854588622606299268753445166094278595146) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 7 +
      30 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_194_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_194_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_195_prefix_zero :
    (∑ x ∈ Finset.range 31,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (195 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (195 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_195_suffix_zero :
    (∑ x ∈ Finset.range 31,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (195 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_195 :
    recurrence5A3Square.coeff 195 =
      (((18525154999457191607976867945439538629780998034019553937159367 * 10 ^ 70 +
        3399246308375386732823591470794107201397977864713150157160542741290606) * 10 ^ 70 +
        0541550666544015390877695442926669895765494946888180752712087473334776) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 6 +
      31 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_195_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_195_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_196_prefix_zero :
    (∑ x ∈ Finset.range 32,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (196 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (196 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_196_suffix_zero :
    (∑ x ∈ Finset.range 32,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (196 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_196 :
    recurrence5A3Square.coeff 196 =
      -(((13642155493564864168801327951141252711060597176702372943301745 * 10 ^ 70 +
        1372836877418335030369345481056357285541438473873664775315050696012610) * 10 ^ 70 +
        8428952499319725181187355720474458726530280358329790169220372948614205) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 5 +
      32 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_196_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_196_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_197_prefix_zero :
    (∑ x ∈ Finset.range 33,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (197 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (197 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_197_suffix_zero :
    (∑ x ∈ Finset.range 33,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (197 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_197 :
    recurrence5A3Square.coeff 197 =
      (((9222556739430457217591477642043334320190993912415588673929429 * 10 ^ 70 +
        8761117695608078945469975531605396282759945780590815082813037157635986) * 10 ^ 70 +
        8110621472275898222800497071759086378856074107190639038055011012874822) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 4 +
      33 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_197_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_197_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_198_prefix_zero :
    (∑ x ∈ Finset.range 34,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (198 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (198 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_198_suffix_zero :
    (∑ x ∈ Finset.range 34,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (198 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_198 :
    recurrence5A3Square.coeff 198 =
      -(((5854962965970539960692350176768358415929564648006178317720213 * 10 ^ 70 +
        2151694220550362963030388092244548740823084130472979477337000291908761) * 10 ^ 70 +
        5336156219102710445194773345608836187031711829284945181457539884581333) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 3 +
      34 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_198_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_198_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_199_prefix_zero :
    (∑ x ∈ Finset.range 35,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (199 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (199 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_199_suffix_zero :
    (∑ x ∈ Finset.range 35,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (199 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_199 :
    recurrence5A3Square.coeff 199 =
      (((3529650839839117481991085417492177795523181220181161657000982 * 10 ^ 70 +
        3549561976029487334648673230148105351152485047431662457157357290520295) * 10 ^ 70 +
        8400904228185774956077976613627476572191493761961954980054012501116194) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 2 +
      35 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_199_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_199_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_200_prefix_zero :
    (∑ x ∈ Finset.range 36,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (200 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (200 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_200_suffix_zero :
    (∑ x ∈ Finset.range 36,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (200 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_200 :
    recurrence5A3Square.coeff 200 =
      -(((2031425359192790476137600652948868417244070351281947479769261 * 10 ^ 70 +
        3496580799191041603442544040164916236768682212680808682257678932317979) * 10 ^ 70 +
        7519199766932589848777544837018274491704959293867659652336132368579047) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 1 +
      36 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_200_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_200_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_201_prefix_zero :
    (∑ x ∈ Finset.range 37,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (201 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (201 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_201_suffix_zero :
    (∑ x ∈ Finset.range 37,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (201 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_201 :
    recurrence5A3Square.coeff 201 =
      (((1118101446674178105072408813795805097084767864609131291870959 * 10 ^ 70 +
        2718483571752904253766009209419277003658275579916106770685716697832346) * 10 ^ 70 +
        8101380399521506760754572810318784663493725641029629761994161692993156) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_201_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_201_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_202_prefix_zero :
    (∑ x ∈ Finset.range 38,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (202 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (202 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_202_suffix_zero :
    (∑ x ∈ Finset.range 38,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (202 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_202 :
    recurrence5A3Square.coeff 202 =
      -(((587776085034489181742722704362152415022671325208888741659143 * 10 ^ 70 +
        7407647591709426007324830850478747383931326856565915243108546491158947) * 10 ^ 70 +
        5770382269619844225999035064787523851079132422340502912342917328363400) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 69 = 31 +
      38 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_202_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_202_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_203_prefix_zero :
    (∑ x ∈ Finset.range 39,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (203 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (203 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_203_suffix_zero :
    (∑ x ∈ Finset.range 39,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (203 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_203 :
    recurrence5A3Square.coeff 203 =
      (((293724495020284414742646707318533091051348636003840799794347 * 10 ^ 70 +
        0848957046153631202925748598011923816653635632768907748713825389404190) * 10 ^ 70 +
        9587573184102620602297883228382699756718449048510737060829855276623504) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 69 = 30 +
      39 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_203_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_203_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_204_prefix_zero :
    (∑ x ∈ Finset.range 40,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (204 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (204 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_204_suffix_zero :
    (∑ x ∈ Finset.range 40,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (204 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_204 :
    recurrence5A3Square.coeff 204 =
      -(((138146235916756014185233960276830315276604659227619718950042 * 10 ^ 70 +
        5621815214009538176359639016930255616691817302773722261190002112407061) * 10 ^ 70 +
        3301498636217317506355315237792281465266561878775536786081262567223106) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 69 = 29 +
      40 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_204_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_204_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_205_prefix_zero :
    (∑ x ∈ Finset.range 41,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (205 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (205 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_205_suffix_zero :
    (∑ x ∈ Finset.range 41,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (205 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_205 :
    recurrence5A3Square.coeff 205 =
      (((59931615319374241767326672524370710038306975290437454049528 * 10 ^ 70 +
        7440097757870403308896179313275423597982904468841654785735738144888850) * 10 ^ 70 +
        7760579398933309833241004641828713496709220593672530267603798516292862) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 69 = 28 +
      41 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_205_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_205_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_206_prefix_zero :
    (∑ x ∈ Finset.range 42,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (206 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (206 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_206_suffix_zero :
    (∑ x ∈ Finset.range 42,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (206 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_206 :
    recurrence5A3Square.coeff 206 =
      -(((22914586769981557950246554087972311189008050161231720830279 * 10 ^ 70 +
        7926597319396733789269471782790881428292590685695793556198707163180052) * 10 ^ 70 +
        0319661169039109044608324629669152682338070708565897518853734000876014) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 69 = 27 +
      42 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_206_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_206_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_207_prefix_zero :
    (∑ x ∈ Finset.range 43,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (207 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (207 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_207_suffix_zero :
    (∑ x ∈ Finset.range 43,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (207 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_207 :
    recurrence5A3Square.coeff 207 =
      (((6731369246930313602685835123634922289792745043722707048388 * 10 ^ 70 +
        0732706282695275527434783660026488741324047999644938363481640863482616) * 10 ^ 70 +
        9749892902928182452770237320994581283328814298508179892579379576435278) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 69 = 26 +
      43 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_207_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_207_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_208_prefix_zero :
    (∑ x ∈ Finset.range 44,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (208 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (208 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_208_suffix_zero :
    (∑ x ∈ Finset.range 44,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (208 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_208 :
    recurrence5A3Square.coeff 208 =
      -(((467110432716333619273927970094717356228540193505189280638 * 10 ^ 70 +
        0073280821615806920862195282976508134186585692154920159147302227396376) * 10 ^ 70 +
        0127659044095977391138687251443728738735081071148392406371533227781138) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 69 = 25 +
      44 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_208_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_208_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_209_prefix_zero :
    (∑ x ∈ Finset.range 45,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (209 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (209 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_209_suffix_zero :
    (∑ x ∈ Finset.range 45,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (209 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_209 :
    recurrence5A3Square.coeff 209 =
      -(((1429763217149544081871020217819506377314314363194472312655 * 10 ^ 70 +
        2704442104185773581299873302702121986794469920239816070555035238922577) * 10 ^ 70 +
        3161167998444256910652466351806593018932792193090182120058384057647620) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 69 = 24 +
      45 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_209_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_209_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_210_prefix_zero :
    (∑ x ∈ Finset.range 46,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (210 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (210 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_210_suffix_zero :
    (∑ x ∈ Finset.range 46,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (210 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_210 :
    recurrence5A3Square.coeff 210 =
      (((1617307332044024782745970452879310057193144124250651412839 * 10 ^ 70 +
        4444739749277732709266995631056153579859771368344941770327622469415568) * 10 ^ 70 +
        6441966623150463089491583774186506059060430442014504040101632580208630) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 69 = 23 +
      46 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_210_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_210_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_211_prefix_zero :
    (∑ x ∈ Finset.range 47,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (211 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (211 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_211_suffix_zero :
    (∑ x ∈ Finset.range 47,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (211 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_211 :
    recurrence5A3Square.coeff 211 =
      -(((1273576612115461003392454228112259966788798432688880640597 * 10 ^ 70 +
        6936558912361851468075072141823349206288764675865241186365954613516729) * 10 ^ 70 +
        2714362406862929629431234780658842875655134603132655628125589694632496) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 69 = 22 +
      47 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_211_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_211_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_212_prefix_zero :
    (∑ x ∈ Finset.range 48,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (212 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (212 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_212_suffix_zero :
    (∑ x ∈ Finset.range 48,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (212 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_212 :
    recurrence5A3Square.coeff 212 =
      (((864229645484271579707317395321720879462866700144347582286 * 10 ^ 70 +
        5833979170191483996272174138365220131189731496669862554024512242952481) * 10 ^ 70 +
        3831928111162587755099597829505962832883481591195493878552608970892129) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 69 = 21 +
      48 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_212_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_212_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_213_prefix_zero :
    (∑ x ∈ Finset.range 49,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (213 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (213 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_213_suffix_zero :
    (∑ x ∈ Finset.range 49,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (213 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_213 :
    recurrence5A3Square.coeff 213 =
      -(((537291077426076647307224153769029499729321498364986281415 * 10 ^ 70 +
        1308785514056070383626003157641489046357813296420328598683772479834389) * 10 ^ 70 +
        7985421111113724447875094722186302111529392023559604933013360383889956) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 69 = 20 +
      49 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_213_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_213_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_214_prefix_zero :
    (∑ x ∈ Finset.range 50,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (214 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (214 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_214_suffix_zero :
    (∑ x ∈ Finset.range 50,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (214 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_214 :
    recurrence5A3Square.coeff 214 =
      (((314118366479036277206287405150093316606508846496231224643 * 10 ^ 70 +
        3499099353601243422945060497297648483885625698913192331188199818615048) * 10 ^ 70 +
        2359436178444118264332469906364503507120249635808556086920529378139176) : ℚ) := by
  unfold recurrence5A3Square
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
    rhs
    rw [show 69 = 19 +
      50 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_214_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_214_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_215_prefix_zero :
    (∑ x ∈ Finset.range 51,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (215 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (215 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_215_suffix_zero :
    (∑ x ∈ Finset.range 51,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (215 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_215 :
    recurrence5A3Square.coeff 215 =
      -(((175012018588993423799011552077475955944490310495376031350 * 10 ^ 70 +
        6273256964686908273041603041432356335896946979170196605165649000144141) * 10 ^ 70 +
        2299682090664432159306488312650284856947184979346659261620976485988898) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 18 +
      51 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_215_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_215_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_216_prefix_zero :
    (∑ x ∈ Finset.range 52,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (216 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (216 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_216_suffix_zero :
    (∑ x ∈ Finset.range 52,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (216 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_216 :
    recurrence5A3Square.coeff 216 =
      (((93624237253306707627581667445594295377018896745704616653 * 10 ^ 70 +
        7153373162677362050465416334983490579363535999500776248494433248403253) * 10 ^ 70 +
        8216001819229903372954493649727480499353752440603151321264818795449888) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 17 +
      52 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_216_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_216_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_217_prefix_zero :
    (∑ x ∈ Finset.range 53,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (217 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (217 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_217_suffix_zero :
    (∑ x ∈ Finset.range 53,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (217 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_217 :
    recurrence5A3Square.coeff 217 =
      -(((48301683586353311190834066546538797934869372262681652681 * 10 ^ 70 +
        6766433316626920552027532818752376308442617859878330833860941722459376) * 10 ^ 70 +
        2916945120679827676284128003840514813396830415645795436370002825720110) : ℚ) := by
  unfold recurrence5A3Square
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
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 16 +
      53 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_217_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_217_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_218_prefix_zero :
    (∑ x ∈ Finset.range 54,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (218 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (218 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_218_suffix_zero :
    (∑ x ∈ Finset.range 54,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (218 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_218 :
    recurrence5A3Square.coeff 218 =
      (((24093216566173387368632616370739996423407835149317026632 * 10 ^ 70 +
        1646908569486428632738759641589487637251118359702920272253950613067396) * 10 ^ 70 +
        1240659926648550910691118398254140804226698902107228458979359754954763) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 219 = 54 +
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
  rw [recurrence5A3Square_coeff_218_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_218_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_219_prefix_zero :
    (∑ x ∈ Finset.range 55,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (219 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (219 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_219_suffix_zero :
    (∑ x ∈ Finset.range 55,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (219 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_219 :
    recurrence5A3Square.coeff 219 =
      -(((11634967875776707200779703184680047438899699745578394664 * 10 ^ 70 +
        3665067275435640215702996276237448686630695241167699497058356162760583) * 10 ^ 70 +
        9297617529956802863052285531563934742393063430503334180415804354372668) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 220 = 55 +
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
  rw [recurrence5A3Square_coeff_219_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_219_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_220_prefix_zero :
    (∑ x ∈ Finset.range 56,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (220 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (220 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_220_suffix_zero :
    (∑ x ∈ Finset.range 56,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (220 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_220 :
    recurrence5A3Square.coeff 220 =
      (((5442226222184442181022090389434098931140587687063668512 * 10 ^ 70 +
        3212941975014319931583593597890625019164956987962300936934450230948893) * 10 ^ 70 +
        0595164195662066107904580517682071005426620000539647367268258574348266) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 221 = 56 +
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
  rw [recurrence5A3Square_coeff_220_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_220_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_221_prefix_zero :
    (∑ x ∈ Finset.range 57,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (221 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (221 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_221_suffix_zero :
    (∑ x ∈ Finset.range 57,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (221 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_221 :
    recurrence5A3Square.coeff 221 =
      -(((2465108799776060159298239468653878378689171468462338266 * 10 ^ 70 +
        4033922956080004122413582367714588462161857783785998194627890438878644) * 10 ^ 70 +
        0254881036569507116881406067943759404679147190750771959268826227231080) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 222 = 57 +
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
  rw [recurrence5A3Square_coeff_221_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_221_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_222_prefix_zero :
    (∑ x ∈ Finset.range 58,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (222 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (222 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_222_suffix_zero :
    (∑ x ∈ Finset.range 58,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (222 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_222 :
    recurrence5A3Square.coeff 222 =
      (((1080416654695396955216837384590593432977152084487628607 * 10 ^ 70 +
        5351069845601064579351605469813805208994374062108528835594639777402731) * 10 ^ 70 +
        8001076633225130037156676121389643820785260787219509680109800172974581) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 223 = 58 +
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
  rw [recurrence5A3Square_coeff_222_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_222_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_223_prefix_zero :
    (∑ x ∈ Finset.range 59,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (223 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (223 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_223_suffix_zero :
    (∑ x ∈ Finset.range 59,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (223 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_223 :
    recurrence5A3Square.coeff 223 =
      -(((457543485806284131044013816400958949230193828866963174 * 10 ^ 70 +
        1212176691362584648481060205714136178004900882611299264566078998326938) * 10 ^ 70 +
        8926132646635553798433425073844365784898365414481822551158778353662890) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 224 = 59 +
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
  rw [recurrence5A3Square_coeff_223_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_223_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_224_prefix_zero :
    (∑ x ∈ Finset.range 60,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (224 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (224 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_224_suffix_zero :
    (∑ x ∈ Finset.range 60,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (224 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_224 :
    recurrence5A3Square.coeff 224 =
      (((186835514282463161218474385329571653255473007466068745 * 10 ^ 70 +
        1736990535502648469029649287251855144628759060159764860680830513223728) * 10 ^ 70 +
        8583433976169974785165586435471184177310826363745540971080773570858511) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 225 = 60 +
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
  rw [recurrence5A3Square_coeff_224_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_224_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_225_prefix_zero :
    (∑ x ∈ Finset.range 61,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (225 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (225 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_225_suffix_zero :
    (∑ x ∈ Finset.range 61,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (225 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_225 :
    recurrence5A3Square.coeff 225 =
      -(((73350452192243548026873980533639164248273316908141114 * 10 ^ 70 +
        8347215043818725235399138572730869609592573060580871711349733752374136) * 10 ^ 70 +
        2965828945300128914676533020393090203337343216062467165316333052023910) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 226 = 61 +
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
  rw [recurrence5A3Square_coeff_225_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_225_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5A3Square_coeff_226_prefix_zero :
    (∑ x ∈ Finset.range 62,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (226 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (226 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_226_suffix_zero :
    (∑ x ∈ Finset.range 62,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (226 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_226 :
    recurrence5A3Square.coeff 226 =
      (((27572018997020516490081561002710623332273845057601440 * 10 ^ 70 +
        3888734135939594201927074789832156959837910715219924742158803638995549) * 10 ^ 70 +
        8591416631759839059855517503321589572056126191379844836319586521784128) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 227 = 62 +
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
  rw [recurrence5A3Square_coeff_226_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_226_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
