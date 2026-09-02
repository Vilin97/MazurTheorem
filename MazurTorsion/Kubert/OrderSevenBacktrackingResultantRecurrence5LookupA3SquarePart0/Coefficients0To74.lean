/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupA3
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupA3SquarePart0Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 5 lookup certificate: A3Square coefficient convolution

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/
public section
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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
