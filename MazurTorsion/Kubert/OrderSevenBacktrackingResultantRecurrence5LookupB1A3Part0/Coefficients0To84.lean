/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupB1
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupA3
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupB1A3Part0Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 5 lookup certificate: B1A3 coefficient convolution

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence5B1_coeff_0
  recurrence5B1_coeff_1
  recurrence5B1_coeff_2
  recurrence5B1_coeff_3
  recurrence5B1_coeff_4
  recurrence5B1_coeff_5
  recurrence5B1_coeff_6
  recurrence5B1_coeff_7
  recurrence5B1_coeff_8
  recurrence5B1_coeff_9
  recurrence5B1_coeff_10
  recurrence5B1_coeff_11
  recurrence5B1_coeff_12
  recurrence5B1_coeff_13
  recurrence5B1_coeff_14
  recurrence5B1_coeff_15
  recurrence5B1_coeff_16
  recurrence5B1_coeff_17
  recurrence5B1_coeff_18
  recurrence5B1_coeff_19
  recurrence5B1_coeff_20
  recurrence5B1_coeff_21
  recurrence5B1_coeff_22
  recurrence5B1_coeff_23
  recurrence5B1_coeff_24
  recurrence5B1_coeff_25
  recurrence5B1_coeff_26
  recurrence5B1_coeff_27
  recurrence5B1_coeff_28
  recurrence5B1_coeff_29
  recurrence5B1_coeff_30
  recurrence5B1_coeff_31
  recurrence5B1_coeff_32
  recurrence5B1_coeff_33
  recurrence5B1_coeff_34
  recurrence5B1_coeff_35
  recurrence5B1_coeff_36
  recurrence5B1_coeff_37
  recurrence5B1_coeff_38
  recurrence5B1_coeff_39
  recurrence5B1_coeff_40
  recurrence5B1_coeff_41
  recurrence5B1_coeff_42
  recurrence5B1_coeff_43
  recurrence5B1_coeff_44
  recurrence5B1_coeff_45
  recurrence5B1_coeff_46
  recurrence5B1_coeff_47
  recurrence5B1_coeff_48
  recurrence5B1_coeff_49
  recurrence5B1_coeff_50
  recurrence5B1_coeff_51
  recurrence5B1_coeff_52
  recurrence5B1_coeff_53
  recurrence5B1_coeff_54
  recurrence5B1_coeff_55
  recurrence5B1_coeff_56
  recurrence5B1_coeff_57
  recurrence5B1_coeff_58
  recurrence5B1_coeff_59
  recurrence5B1_coeff_60
  recurrence5B1_coeff_61
  recurrence5B1_coeff_62
  recurrence5B1_coeff_63

attribute [local simp]
  recurrence5B1_coeff_64
  recurrence5B1_coeff_65
  recurrence5B1_coeff_66
  recurrence5B1_coeff_67
  recurrence5B1_coeff_68
  recurrence5B1_coeff_69
  recurrence5B1_coeff_70
  recurrence5B1_coeff_71
  recurrence5B1_coeff_72
  recurrence5B1_coeff_73
  recurrence5B1_coeff_74
  recurrence5B1_coeff_75
  recurrence5B1_coeff_76
  recurrence5B1_coeff_77
  recurrence5B1_coeff_78
  recurrence5B1_coeff_79
  recurrence5B1_coeff_80
  recurrence5B1_coeff_81
  recurrence5B1_coeff_82
  recurrence5B1_coeff_83
  recurrence5B1_coeff_84
  recurrence5B1_coeff_85
  recurrence5B1_coeff_86
  recurrence5B1_coeff_87
  recurrence5B1_coeff_88
  recurrence5B1_coeff_89
  recurrence5B1_coeff_90
  recurrence5B1_coeff_91
  recurrence5B1_coeff_92
  recurrence5B1_coeff_93
  recurrence5B1_coeff_94
  recurrence5B1_coeff_95
  recurrence5B1_coeff_96
  recurrence5B1_coeff_97
  recurrence5B1_coeff_98
  recurrence5B1_coeff_99
  recurrence5B1_coeff_100
  recurrence5B1_coeff_101
  recurrence5B1_coeff_102
  recurrence5B1_coeff_103
  recurrence5B1_coeff_104
  recurrence5B1_coeff_105
  recurrence5B1_coeff_106
  recurrence5B1_coeff_107
  recurrence5B1_coeff_108
  recurrence5B1_coeff_109
  recurrence5B1_coeff_110
  recurrence5B1_coeff_111
  recurrence5B1_coeff_112
  recurrence5B1_coeff_113
  recurrence5B1_coeff_114
  recurrence5B1_coeff_115
  recurrence5B1_coeff_116
  recurrence5B1_coeff_117
  recurrence5B1_coeff_118
  recurrence5B1_coeff_119
  recurrence5B1_coeff_120
  recurrence5B1_coeff_121
  recurrence5B1_coeff_122
  recurrence5B1_coeff_123
  recurrence5B1_coeff_124
  recurrence5B1_coeff_125
  recurrence5B1_coeff_126
  recurrence5B1_coeff_127

attribute [local simp]
  recurrence5B1_coeff_128
  recurrence5B1_coeff_129
  recurrence5B1_coeff_130
  recurrence5B1_coeff_131
  recurrence5B1_coeff_132
  recurrence5B1_coeff_133
  recurrence5B1_coeff_134
  recurrence5B1_coeff_135
  recurrence5B1_coeff_136
  recurrence5B1_coeff_137
  recurrence5B1_coeff_138
  recurrence5B1_coeff_139
  recurrence5B1_coeff_140
  recurrence5B1_coeff_141
  recurrence5B1_coeff_142
  recurrence5B1_coeff_143
  recurrence5B1_coeff_144
  recurrence5B1_coeff_145
  recurrence5B1_coeff_146
  recurrence5B1_coeff_147
  recurrence5B1_coeff_148
  recurrence5B1_coeff_149
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

attribute [local simp]
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

attribute [local simp]
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

theorem recurrence5B1A3_coeff_0 :
    recurrence5B1A3.coeff 0 =
      (0 : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_1 :
    recurrence5B1A3.coeff 1 =
      -((5504 * 10 ^ 70 +
        2264712803397541033003458089436964882284165860489944173288987361806592) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_2 :
    recurrence5B1A3.coeff 2 =
      ((42587536 * 10 ^ 70 +
        9717172543884304050105072712305572161662063535986125885125197180414464) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_3 :
    recurrence5B1A3.coeff 3 =
      -((155597302421 * 10 ^ 70 +
        9506376789139276916854255998721742107056781414768369641482575007053024) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_4 :
    recurrence5B1A3.coeff 4 =
      ((331520747768196 * 10 ^ 70 +
        0560435891357521163071968719694820283206375355165058162043805943220860) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_5 :
    recurrence5B1A3.coeff 5 =
      -((442909232982487068 * 10 ^ 70 +
        3276642647535733631244200323290489776628411762208509589335103585221116) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_6 :
    recurrence5B1A3.coeff 6 =
      ((373523606780616448100 * 10 ^ 70 +
        1703526790267805245915224613166719023551519244947507191463843200645712) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_7 :
    recurrence5B1A3.coeff 7 =
      -((186062682881037853348858 * 10 ^ 70 +
        9692860735328781931750729747469270378563278558282116000271972216462996) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_8 :
    recurrence5B1A3.coeff 8 =
      ((35568261704251459638146205 * 10 ^ 70 +
        3414162109490828180555778516116628790963337922140842852137079405843120) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_9 :
    recurrence5B1A3.coeff 9 =
      ((19720215329700880686020606553 * 10 ^ 70 +
        1311900948379669333109150781517399831585317585094175419491050751285712) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_10 :
    recurrence5B1A3.coeff 10 =
      -((21807665312708647818933873513819 * 10 ^ 70 +
        9064980614654282825193078148300609320429911644572565149089558925148244) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_11 :
    recurrence5B1A3.coeff 11 =
      ((13397327238285791792720615431283036 * 10 ^ 70 +
        5192060160142074420089915684524403120446657862503532450908032941842552) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_12 :
    recurrence5B1A3.coeff 12 =
      -((7026890499389508133571852079262215386 * 10 ^ 70 +
        6395711957638704698032164130424118297660806345950008801793556473732704) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_13 :
    recurrence5B1A3.coeff 13 =
      ((3051678794810780394670757151781004951260 * 10 ^ 70 +
        6177132742472185422124561194643765414023226883343022868844232975733586) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_14 :
    recurrence5B1A3.coeff 14 =
      -((913629117653031457920892933854537841370928 * 10 ^ 70 +
        9799972441780754981553900743966253658812566835255004781658504374135141) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_15 :
    recurrence5B1A3.coeff 15 =
      ((90113132271343575564151581017215151227024393 * 10 ^ 70 +
        9974214297326757312354746881180521288253415981736592852841302850992283) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_16 :
    recurrence5B1A3.coeff 16 =
      ((79296442504860765757875098152158354577401501997 * 10 ^ 70 +
        9257030632327784597145981142048778049264570401275320690644183353212834) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_17 :
    recurrence5B1A3.coeff 17 =
      -((57174583600568932917900047365970509436867034780231 * 10 ^ 70 +
        7690647831338248048057452812877715491013093911973058665830546760481555) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_18 :
    recurrence5B1A3.coeff 18 =
      ((22745180860381834975334399883176158271412383258501185 * 10 ^ 70 +
        9649587252191870223956119734040074822618921055048194768599419555039090) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_19 :
    recurrence5B1A3.coeff 19 =
      -((6612668281231003742890401923774762585581282688889507184 * 10 ^ 70 +
        2132059846336571793170667581476810237183449321411853925762192090896864) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_20 :
    recurrence5B1A3.coeff 20 =
      ((1517101879717945486323687980503866963333602428813848351145 * 10 ^ 70 +
        0838648397966087717607586506754390582069882402845805118210659640498965) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_21 :
    recurrence5B1A3.coeff 21 =
      -((283459615979962867235846171323412744722389705896749985422140 * 10 ^ 70 +
        4546604156909290961401958063029124092169513119563464717020657635446788) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_22 :
    recurrence5B1A3.coeff 22 =
      ((43656254805453668633209244995725026297268929733243525731289542 * 10 ^ 70 +
        9114451196822688016375029487734830615103907185600640318374820718701421) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_23 :
    recurrence5B1A3.coeff 23 =
      -((5524739770779271337861245860344083419891081750400733533718375423 * 10 ^ 70 +
        4618259412901261055607666332805502021940404013574427626895784158079348) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_24 :
    recurrence5B1A3.coeff 24 =
      ((559531488118453934170363029714965625989411413846845198674278909195 * 10 ^ 70 +
        5649578498106164167550774065484722032350155107033254956899971133661734) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_25 :
    recurrence5B1A3.coeff 25 =
      -((41389535787512810699411523601647996590729443727385909042543014864071 * 10 ^ 70 +
        2778720411680595580816092620657999099038706656756199591804571846467280) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_26 :
    recurrence5B1A3.coeff 26 =
      ((1338439888377084003734328248014010044538116661384686245700894395095949 * 10 ^ 70 +
        8612720909242449532739396681737316879889362616103946113609054722256704) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_27 :
    recurrence5B1A3.coeff 27 =
      (((20 * 10 ^ 70 +
        0715676449913136827486570793727574528710417768474869641265472349456124) * 10 ^ 70 +
        1858545408737909931659557148316583760714815934447543902635080413493703) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_28 :
    recurrence5B1A3.coeff 28 =
      -(((4867 * 10 ^ 70 +
        4307296749701995182339763930520029901812319220321442856722551449177669) * 10 ^ 70 +
        9819974307582529916199945806679640149076620526432823140775390604832787) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_29 :
    recurrence5B1A3.coeff 29 =
      (((648563 * 10 ^ 70 +
        2779339646927126249512755108034915973366883844411848656189238923644831) * 10 ^ 70 +
        2821710194140080963786326435625310924223049362962790668534083046496153) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_30 :
    recurrence5B1A3.coeff 30 =
      -(((66747710 * 10 ^ 70 +
        6760466004153520045846442454243807735401006413557533036691691634206468) * 10 ^ 70 +
        5250282282268531719148728136916834608796255074733551696699721890201009) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_31 :
    recurrence5B1A3.coeff 31 =
      (((5767318273 * 10 ^ 70 +
        4018887367803687515720746233034291555829725225091394032783707239996023) * 10 ^ 70 +
        0792069205146453242041862232875653534396633411249573422884520723296192) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_32 :
    recurrence5B1A3.coeff 32 =
      -(((433283354643 * 10 ^ 70 +
        5095865597082619219796197448495672839467716594335609546138806892383248) * 10 ^ 70 +
        3811883772834029476451746700960714074404391476045204265446978366954758) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_33 :
    recurrence5B1A3.coeff 33 =
      (((28839709055210 * 10 ^ 70 +
        6747836875581697921306593509587042861654491548279374058863069915513559) * 10 ^ 70 +
        2016153275711473972933689599358698155947488439177352527000645014863990) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_34 :
    recurrence5B1A3.coeff 34 =
      -(((1720687824965896 * 10 ^ 70 +
        2285541305156360545258487275373162063869067908339693217429388358962774) * 10 ^ 70 +
        4857732806382757320311624034709210647041678326615130343192192441548502) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_35 :
    recurrence5B1A3.coeff 35 =
      (((92763348223776605 * 10 ^ 70 +
        7217281807704224946432025752958178612071798419452295353348935878465676) * 10 ^ 70 +
        4111873936381900154847648905735376819825612612908009365812867246396161) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_36 :
    recurrence5B1A3.coeff 36 =
      -(((4545140493345419681 * 10 ^ 70 +
        3080090266980233282878426531021931184198613603158504985301340699765514) * 10 ^ 70 +
        6231145103527094494648077206164745835963621859058716965252109145289811) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_37 :
    recurrence5B1A3.coeff 37 =
      (((203301956987773374884 * 10 ^ 70 +
        5554033547741024952688395245576590327649784741423451882819991991784944) * 10 ^ 70 +
        7691368500011493390983043166193160919633287407917130584932749588349165) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_38 :
    recurrence5B1A3.coeff 38 =
      -(((8330200867065412166885 * 10 ^ 70 +
        9886418932565125788764772111373438534091644847420897381444555540037022) * 10 ^ 70 +
        9632577921409223877406432781763743382378789921234030606039412903944803) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_39 :
    recurrence5B1A3.coeff 39 =
      (((313509026112289852303728 * 10 ^ 70 +
        9246474025295439551235627795993080523230550836222418226871404002778228) * 10 ^ 70 +
        4390085032481745384272054933597305067690820947605076396204897836142682) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_40 :
    recurrence5B1A3.coeff 40 =
      -(((10859186785124759129556887 * 10 ^ 70 +
        1154954322192855294009603888777673177027206740628649279087760365611696) * 10 ^ 70 +
        8328914477156660804392325392307996427222436635534067030634225360085421) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_41 :
    recurrence5B1A3.coeff 41 =
      (((346649924777258686237655481 * 10 ^ 70 +
        5621077902103465810976705719844599610215798516875776752144922195242402) * 10 ^ 70 +
        0436646287284878260330809666392841668291015203761186754094070458548639) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_42 :
    recurrence5B1A3.coeff 42 =
      -(((10205271417499961464491703591 * 10 ^ 70 +
        4507917696680338254158803662074449504976077219249069293332548925488591) * 10 ^ 70 +
        6233412826982220757622654255785384383597078526272439355712857646096840) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_43 :
    recurrence5B1A3.coeff 43 =
      (((277029323099026165645163944858 * 10 ^ 70 +
        7520707075069548152080873436876611762430283456230612554291232008686202) * 10 ^ 70 +
        6767575060194601333432170968912087632461496495100795021304946646507770) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_44 :
    recurrence5B1A3.coeff 44 =
      -(((6925147251046618592909127668802 * 10 ^ 70 +
        6155239388076350898663489294778267762060209545338853124507345770661853) * 10 ^ 70 +
        2631042512500342128208186802380992078283152249810642678958472964537294) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_45 :
    recurrence5B1A3.coeff 45 =
      (((158938518652354295836553445662152 * 10 ^ 70 +
        6811535042296264700507311866587320704000195550258419937282889856305118) * 10 ^ 70 +
        9381168914283409761828520751766934614437423778218724537525588003987955) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_46 :
    recurrence5B1A3.coeff 46 =
      -(((3329619461878612067717366420623354 * 10 ^ 70 +
        1332816833236972730982207265862267732306532984703730003142664968013095) * 10 ^ 70 +
        4623291132435262695049015512237679501109781183080969971713041358630728) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_47 :
    recurrence5B1A3.coeff 47 =
      (((62967483793365217072507207403237399 * 10 ^ 70 +
        5746688910301789155088145922050187531068160944215261414584357673067551) * 10 ^ 70 +
        8066457052133577866435281457677350685672493504549577610770866072270134) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_48 :
    recurrence5B1A3.coeff 48 =
      -(((1051232663077559498133754774938291193 * 10 ^ 70 +
        0970552575828536309694099103839602382443233505514494948161877204677143) * 10 ^ 70 +
        1024774818218297108056557845900580169458551353258164235219810296929222) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_49 :
    recurrence5B1A3.coeff 49 =
      (((14704487461541183949551623518601285951 * 10 ^ 70 +
        8815415777506161048639521285334843441572862070325678044982655245658951) * 10 ^ 70 +
        0297895245746974421523802550576938244352366739238056121461671689353071) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_50 :
    recurrence5B1A3.coeff 50 =
      -(((145266485616576043451501025797823912955 * 10 ^ 70 +
        1772226278008159257578642124947739616866819627875259900499860720899410) * 10 ^ 70 +
        2562628597377393344446781392866899225736240398680542596760633107209141) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_51 :
    recurrence5B1A3.coeff 51 =
      -(((25590276165410337253251703737672495807 * 10 ^ 70 +
        5605328535841468341954152400837571737138281451757328948622514690325876) * 10 ^ 70 +
        4654742376076052325962489650214653378001307144597938024931911747951869) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_52 :
    recurrence5B1A3.coeff 52 =
      (((49412119761019514011879658509972026347547 * 10 ^ 70 +
        1667084387722067227916105573022584795962088968507691511030444451091090) * 10 ^ 70 +
        6677924651048948028595996347370601207743587482319121089365286392644215) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_53 :
    recurrence5B1A3.coeff 53 =
      -(((1658586425651782179407004336694245168880389 * 10 ^ 70 +
        1376572797712700710062410606049939367779320260180511454283006116487893) * 10 ^ 70 +
        0596408658639716923211094875986477829557144175026382234983102834984472) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_54 :
    recurrence5B1A3.coeff 54 =
      (((39758350760236533502883235319342055300264303 * 10 ^ 70 +
        5354783606521914966933662614003984427827410338504218683561019853907716) * 10 ^ 70 +
        5394535893584328825892942779830235371846826934708527966538060554004630) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_55 :
    recurrence5B1A3.coeff 55 =
      -(((805686006775677924082307149486258197986047357 * 10 ^ 70 +
        2633052201546974903231203665351577185752468145736640909758540977108689) * 10 ^ 70 +
        8468521109350030262463400048647319746110997484724831845177546552750305) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_56 :
    recurrence5B1A3.coeff 56 =
      (((14565617092253083013610840595092968272624372833 * 10 ^ 70 +
        8024587304081405810800798776469601975165838253428692700736925910220380) * 10 ^ 70 +
        7720113332768925292668598935715226744817907535162948522279389985975482) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_57 :
    recurrence5B1A3.coeff 57 =
      -(((240761761715156970261920647565496384643482856923 * 10 ^ 70 +
        2607179411432535002343210912599305897568118157898626320724231471256432) * 10 ^ 70 +
        9092921227760398525790377355490317712336304396327020856960216776704552) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_58 :
    recurrence5B1A3.coeff 58 =
      (((3688307813884143041768442485738630135008182165557 * 10 ^ 70 +
        7896534737161346481110444924649325681775572380214372923446096123032438) * 10 ^ 70 +
        9324902346976159289707424624715291329511300639165159482258336601717840) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_59 :
    recurrence5B1A3.coeff 59 =
      -(((52810091297871420103671092563739478889532702885378 * 10 ^ 70 +
        5454940816879070789428693210390574521049125004095606606183512630707312) * 10 ^ 70 +
        4282013869953384209660764932964894123928445213091297690255475108607908) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_60 :
    recurrence5B1A3.coeff 60 =
      (((710809083884556308360878487505551514402233917603331 * 10 ^ 70 +
        7213940896999207791869687373290126962345619020376237637943025503790016) * 10 ^ 70 +
        8998290275369659619733272884841499141139005507560205228299975079375477) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_61 :
    recurrence5B1A3.coeff 61 =
      -(((9031281747180055170180106681055861468120216962903283 * 10 ^ 70 +
        2524820924319982273703085483118562244983956717895055048233222179051401) * 10 ^ 70 +
        0819286183903906226617399644809322891580250585303878160327675929171809) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_62 :
    recurrence5B1A3.coeff 62 =
      (((108666160713993419158882846920784180129779093457735368 * 10 ^ 70 +
        7129366970283256920042046982908573565492642111853734786494750008133050) * 10 ^ 70 +
        4351279161658454513550385780889324415336857576056349039680071288766619) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_63 :
    recurrence5B1A3.coeff 63 =
      -(((1241350824397694838179757329953134003047187050782137709 * 10 ^ 70 +
        8171863039222089314865716574864001060911836245752151449554018302652873) * 10 ^ 70 +
        2969043951004919904107543791119115913927288647006390703944745276057912) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_64 :
    recurrence5B1A3.coeff 64 =
      (((13491560636999264275441625101549264543517644517169169040 * 10 ^ 70 +
        6677133122515131235912228691750148429967941888830073853422379555368464) * 10 ^ 70 +
        4861565430706643875082916657529040927066614201659560202431883160916903) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_65 :
    recurrence5B1A3.coeff 65 =
      -(((139755699880462831542041368303631136783901093081214162806 * 10 ^ 70 +
        5179854749810517141010783742823949768348023983711463026086922310515740) * 10 ^ 70 +
        5761937467409030816165713523645421060523539352621848737135712578650838) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_66 :
    recurrence5B1A3.coeff 66 =
      (((1381926149922224789880303092613648330982299102729178428534 * 10 ^ 70 +
        9173043507261081160616368364748589122514475206059647181348001285979868) * 10 ^ 70 +
        9603388279212225199650171814014555419535494908296355818700499168547906) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_67 :
    recurrence5B1A3.coeff 67 =
      -(((13061614346368689944522003835169021456512824192822951334087 * 10 ^ 70 +
        1476421537189174396860449461065767256711326407960109483193757456459796) * 10 ^ 70 +
        3503959553764357397744206443474965215430455173871911935805721797009247) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_68 :
    recurrence5B1A3.coeff 68 =
      (((118149514184016967559662129526559916943727332219987332670365 * 10 ^ 70 +
        5172456971223463621882478643466486777165312650432860158412122089537010) * 10 ^ 70 +
        1779600556746566019476933317027127606981039188588749079460444377343995) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_69 :
    recurrence5B1A3.coeff 69 =
      -(((1023920726036051761081083196226781423310747300817562261775897 * 10 ^ 70 +
        2619653827911420025708902752319842163541038953984559831638330665705809) * 10 ^ 70 +
        6704573555566107964823244004090433175529124631968904732946652056567081) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_70 :
    recurrence5B1A3.coeff 70 =
      (((8510111299988950968996846790225208628703073360965327996587064 * 10 ^ 70 +
        6324337587570214737233695183365741956687020535483234365905967775349268) * 10 ^ 70 +
        6959583362382884356274916365072130870220846450210733415526150855242194) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_71 :
    recurrence5B1A3.coeff 71 =
      -(((67895282988001361662598924853344159317338747224704737867907018 * 10 ^ 70 +
        4039470515455417071705656785473014809614099535992318640981833299498705) * 10 ^ 70 +
        0291838208354688582107270324121273518020151346568714217391622775777648) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_72 :
    recurrence5B1A3.coeff 72 =
      (((520416784247082673079246353090252076972789055644058130822742951 * 10 ^ 70 +
        0651769350653670897516670693566757796580430205958404471244541194948292) * 10 ^ 70 +
        7464242427386623289452495591611684123878075851033166591081378433328271) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_73 :
    recurrence5B1A3.coeff 73 =
      -(((3835457215825383973500190627253167853282474702202057458110983059 * 10 ^ 70 +
        8311735216199081796105933653824348935845255949390175657933306335230297) * 10 ^ 70 +
        1716626777314794765110558909504896720840994663099270181625441975914763) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_74 :
    recurrence5B1A3.coeff 74 =
      (((27199573794884910455943445629575598028547126483942916103248213689 * 10 ^ 70 +
        2996730556185195036402146217902340148075759434011795943288771197429774) * 10 ^ 70 +
        7547142535658784641627069508272063337586621527079806453916896496731248) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_75 :
    recurrence5B1A3.coeff 75 =
      -(((185734155797373117251154624504166070014986209511354648704693579503 * 10 ^ 70 +
        7559105655789285836346565675349426920003995007313370043099072871688229) * 10 ^ 70 +
        7457028213123846567154198932011119251740983822566801649156152850704594) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_76 :
    recurrence5B1A3.coeff 76 =
      (((1222065535932334196587677370288369101289988600754108878941306985709 * 10 ^ 70 +
        8932729895336690466251717003063987906778910243752931352018523116553757) * 10 ^ 70 +
        9247547234558539975119017269698150656768027780739356775249751488159669) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_77 :
    recurrence5B1A3.coeff 77 =
      -(((7752521327391588269116738652845569235582885296132586334109983867860 * 10 ^ 70 +
        9439308248652537355670386341405818371247848886372376412630212626991296) * 10 ^ 70 +
        2260470482732104832943146598233185195283088590609154970528682527387999) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_78 :
    recurrence5B1A3.coeff 78 =
      (((47445571520795835526052831836557061612949690069159703130352907344117 * 10 ^ 70 +
        0081042553540686964064820082754049728624422585550287559994045634663398) * 10 ^ 70 +
        6291143867482499213307296323404557469081484307289402776630875412407884) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_79 :
    recurrence5B1A3.coeff 79 =
      -(((280283841917197880072020681889261902666978070498150830887185506238848 * 10 ^ 70 +
        8258822935789505910514366451079472949139352162593596705784958837344937) * 10 ^ 70 +
        1444858768707278201719598081746704391882162128722845191147155551401724) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_80 :
    recurrence5B1A3.coeff 80 =
      (((1599128851971047963663856421959878776384936057227016342084774291815304 * 10 ^ 70 +
        3935063545903602004082439318406609666680141366936191400164453151000876) * 10 ^ 70 +
        9363868594525664168529314684322370225526383425478195444015420329501897) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_81 :
    recurrence5B1A3.coeff 81 =
      -(((8816048898462384899440668719012178641337641222814598566474647630282285 * 10 ^ 70 +
        9906812967162217235982787850186809313945379618196219740587652179779275) * 10 ^ 70 +
        8935335798963430115707807378017406950917182491977747688535111951175236) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_82 :
    recurrence5B1A3.coeff 82 =
      ((((4 * 10 ^ 70 +
        6987383694659164011425179702072539063408888821054696407640293140550444) * 10 ^ 70 +
        6984814021048228036860531506552744256602016857486791288427901719944118) * 10 ^ 70 +
        3857002775086997620630039629400228790669403417322916945712683112449469) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_83 :
    recurrence5B1A3.coeff 83 =
      -((((24 * 10 ^ 70 +
        2218333843011086850365449861829619722990424827734014502831540525455288) * 10 ^ 70 +
        3277891014610787448152531531854690307455883797090824609895708516166079) * 10 ^ 70 +
        9299761333833983667865403277683827031823731987638173028815504776635830) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_84 :
    recurrence5B1A3.coeff 84 =
      ((((120 * 10 ^ 70 +
        8213414169395862555966203834141756764600402110577373938236812234666845) * 10 ^ 70 +
        3773321401150747489763381726582583202031153507147285137130450693215459) * 10 ^ 70 +
        0989329893697123609439088766007307496380249462780959447698980106108934) : ℚ) := by
  unfold recurrence5B1A3
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
