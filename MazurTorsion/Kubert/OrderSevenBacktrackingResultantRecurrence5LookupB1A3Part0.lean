/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupB1
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupA3
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 5 lookup certificate: B1A3 coefficient convolution

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

theorem recurrence5B1A3_coeff_85 :
    recurrence5B1A3.coeff 85 =
      -((((583 * 10 ^ 70 +
        4112284198351127095233566696718057505994875879832374911719914649152247) * 10 ^ 70 +
        4656005696401653886811004260597414059341717154855161588851056611039959) * 10 ^ 70 +
        8693981687757376891966040958710902012537209088039616994075040950947389) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_86 :
    recurrence5B1A3.coeff 86 =
      ((((2728 * 10 ^ 70 +
        1963733205860919506352356929592271520326579548728700792570676679183047) * 10 ^ 70 +
        1456477118850293743545424813800809229063994494429396298342429196367957) * 10 ^ 70 +
        7911618217584595934652142672075523248804108049500883921189005526131825) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_87 :
    recurrence5B1A3.coeff 87 =
      -((((12359 * 10 ^ 70 +
        8568507677795312482920369090650721135988273592512529923533136602501859) * 10 ^ 70 +
        3979687683213270259837035133185935603763255716724805274865848028109582) * 10 ^ 70 +
        2729063287015525337342058254988180840462847858098558318612398297156675) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_88 :
    recurrence5B1A3.coeff 88 =
      ((((54268 * 10 ^ 70 +
        5080485608589324972252045511974460612469892088717365779269270659325407) * 10 ^ 70 +
        2731866254473611134749244729483962329876850312842406170171211187577870) * 10 ^ 70 +
        4943867545765318824027756834617007572125352612748207100798522489154179) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_89 :
    recurrence5B1A3.coeff 89 =
      -((((231010 * 10 ^ 70 +
        3042515716170651694572806161872911465777997575966022927410997515377008) * 10 ^ 70 +
        6004926731771845125635746978204644955064358780704783617910961520101875) * 10 ^ 70 +
        2726223355596659003265709557467840548046107747954673989032372111414916) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_90 :
    recurrence5B1A3.coeff 90 =
      ((((953694 * 10 ^ 70 +
        5747777633109735922391804146150870384615760510351089394994678499387412) * 10 ^ 70 +
        7983962212039696066037500258249001177344330583444059286235967977391870) * 10 ^ 70 +
        1076916168900851040663182637324790491896910221631109466407242462505222) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_91 :
    recurrence5B1A3.coeff 91 =
      -((((3819623 * 10 ^ 70 +
        7010926166662361659455533500579114190053573902431803006820751404061707) * 10 ^ 70 +
        1967775808872558317668286694523085816016313005740139856824169760902186) * 10 ^ 70 +
        5403080412180401046632726695526055787553834912331329476258783423218904) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_92 :
    recurrence5B1A3.coeff 92 =
      ((((14845594 * 10 ^ 70 +
        9133780704681239976933351378832663191492349559084918820170145164285049) * 10 ^ 70 +
        5855063591517999613663632162138126891537032110311449837554442243278377) * 10 ^ 70 +
        3891496354617303825153856940995588870073923101826547120362810448077771) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_93 :
    recurrence5B1A3.coeff 93 =
      -((((56010150 * 10 ^ 70 +
        4585178307140978260110368865779579879867602896296588261872432557915053) * 10 ^ 70 +
        2195583512201271622021678278032340477976136622933436429984689362992246) * 10 ^ 70 +
        3634453083496116622015905424486112042473113270399527907163875369709144) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_94 :
    recurrence5B1A3.coeff 94 =
      ((((205186352 * 10 ^ 70 +
        7466699874722272464147607838519662180823605886087953622604451339749716) * 10 ^ 70 +
        8371230329216172398547437658140787306908261978193054754414364502333815) * 10 ^ 70 +
        4872012627411620936147472472297510499515055901294791680610678552115685) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_95 :
    recurrence5B1A3.coeff 95 =
      -((((730058521 * 10 ^ 70 +
        9873842703708054348813940608418627769518053746473498137676124474619393) * 10 ^ 70 +
        6397930781439403838339695826603905290384949315072594067679840904642686) * 10 ^ 70 +
        9416278942959382136052840594536772472470590103306084361787824704200461) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_96 :
    recurrence5B1A3.coeff 96 =
      ((((2523502978 * 10 ^ 70 +
        5918249168749644197080535478485286434228729556513373620663264243781966) * 10 ^ 70 +
        6680490579791237865527163161870123168057054681571381256889941523829916) * 10 ^ 70 +
        7259454778095095067095204141837330267679257716073381607933291834980210) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_97 :
    recurrence5B1A3.coeff 97 =
      -((((8476004890 * 10 ^ 70 +
        1586269579490959465027993577011922592036741397944446633410613765255630) * 10 ^ 70 +
        6633214514446584215675679468277602746031188934921055252568175475310821) * 10 ^ 70 +
        0218746686285605258136291892694092311628300160436477437282563635029720) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_98 :
    recurrence5B1A3.coeff 98 =
      ((((27670633668 * 10 ^ 70 +
        1774731392431133683778655268578558754308608770650713598097833232228233) * 10 ^ 70 +
        4544244026549548548660007687518655762667581863026079238576972001504938) * 10 ^ 70 +
        3834772320792353397916444201199775851459993455249912826410430919587278) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_99 :
    recurrence5B1A3.coeff 99 =
      -((((87817696447 * 10 ^ 70 +
        3865385470916618609125362790950984989133766978332579799851112011474148) * 10 ^ 70 +
        7135382398641059092048519008350327204648042338535423943957294122467421) * 10 ^ 70 +
        7163245812605770629085035831887786466019961835554187812043816846198500) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_100 :
    recurrence5B1A3.coeff 100 =
      ((((271000371901 * 10 ^ 70 +
        7282260954538285220057174633068475990265980505597392412684566584088850) * 10 ^ 70 +
        2893376102148893692601430364462045174643617706453561779866903885752132) * 10 ^ 70 +
        0495253548368774977382432736808646139030713387981545103183829291912454) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_101 :
    recurrence5B1A3.coeff 101 =
      -((((813332389978 * 10 ^ 70 +
        9238631139470732566987807729087880805373256292696676688401247994337786) * 10 ^ 70 +
        2562414504489681444312851197457402669319249495095713004587327086033883) * 10 ^ 70 +
        8168690733807389940061417455319546983328513295404645142215719714203409) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_102 :
    recurrence5B1A3.coeff 102 =
      ((((2374420916745 * 10 ^ 70 +
        4189897722676056939009669386305691230387955631385808730865390615097656) * 10 ^ 70 +
        9806693791328676896881089049377007795841044634557743632727937391834640) * 10 ^ 70 +
        5346099704321615632547819688805088816070177715610312402510339050117123) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_103 :
    recurrence5B1A3.coeff 103 =
      -((((6743972333277 * 10 ^ 70 +
        7983677500625395210610366665457571350207879721727362602978845138721232) * 10 ^ 70 +
        0274749375564550397573651528789223581321106381753044867515773791528688) * 10 ^ 70 +
        6793869079309497195045988085815388537550006206695470729784123477318075) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_104 :
    recurrence5B1A3.coeff 104 =
      ((((18638683001599 * 10 ^ 70 +
        6749996190913969612056993083568491293362996970710201778001610875923891) * 10 ^ 70 +
        4420129325093929120423279828917186712433146896074969457343323315712777) * 10 ^ 70 +
        6797745773362743451229792359382035786312615927223759270677222182774216) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_105 :
    recurrence5B1A3.coeff 105 =
      -((((50133158923891 * 10 ^ 70 +
        1016060546787566434019322448864287547170732179469645625189824532311935) * 10 ^ 70 +
        3895119378084566631690908270525510593659545594584063258778992860725609) * 10 ^ 70 +
        5682624289348641218804947106843446484054040433960450596520253755904204) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_106 :
    recurrence5B1A3.coeff 106 =
      ((((131253398679735 * 10 ^ 70 +
        4548312108063435553054865105248293464560217982204423694767448996789060) * 10 ^ 70 +
        7840533665673454977470652198237490943603699073643717873722283585921100) * 10 ^ 70 +
        9289871888409068903880606710658838666753751285288658951171073657435069) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_107 :
    recurrence5B1A3.coeff 107 =
      -((((334528563034022 * 10 ^ 70 +
        7139366397313332660814983158585273049580851776192035767686823813978292) * 10 ^ 70 +
        0697676478593283434144587752106555020130395071658971379274876030264169) * 10 ^ 70 +
        5348353955673332659566532481459790657721757197749079664403762757276308) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_108 :
    recurrence5B1A3.coeff 108 =
      ((((830139157663667 * 10 ^ 70 +
        1002734817031623608032885289486681541452052265560566647102977854977923) * 10 ^ 70 +
        8924712410983318828986647246169898493367556698160972271058257502129277) * 10 ^ 70 +
        4522594283889808451496305425296588484172679891526267949771961213261413) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_109 :
    recurrence5B1A3.coeff 109 =
      -((((2005940097441560 * 10 ^ 70 +
        5634643029097873256343308823543434325420321157969141568036484977389798) * 10 ^ 70 +
        1259528868497399521720556746055087271159240596021637658594241125381286) * 10 ^ 70 +
        9664482180722534546853119507708116293019927917650242400626439662394211) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_110 :
    recurrence5B1A3.coeff 110 =
      ((((4720469294229664 * 10 ^ 70 +
        4854059497186039265369633611025259793363891703607950510337455199668520) * 10 ^ 70 +
        6191770313822747919038158573892113350480068191770324962853571365917615) * 10 ^ 70 +
        3654001362228064476917608108319783492401780715429883945825228141090844) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_111 :
    recurrence5B1A3.coeff 111 =
      -((((10819317128116350 * 10 ^ 70 +
        1194966071691940207114141405318361457870317305304906295395679841272137) * 10 ^ 70 +
        6546453369633917900635737742181659518269755361528404962354627393300516) * 10 ^ 70 +
        2888210977500204244737769971829933946170817093346918921174496304325827) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_112 :
    recurrence5B1A3.coeff 112 =
      ((((24154930843241183 * 10 ^ 70 +
        4868594366690770324902883916483320810358211170924603418962301206412914) * 10 ^ 70 +
        3402956774012382684452431833142384699479448326829419730941245307891815) * 10 ^ 70 +
        0815849949303610505146162169101854489963204749969285223782099641657627) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_113 :
    recurrence5B1A3.coeff 113 =
      -((((52534348337817039 * 10 ^ 70 +
        5718490747005623282664991730005530573833862970707426615541920142527297) * 10 ^ 70 +
        9767398106786606751645290383348231810897124988291693827541013959496811) * 10 ^ 70 +
        4135353354236421263192257264699927897690990029334802801862106789361598) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_114 :
    recurrence5B1A3.coeff 114 =
      ((((111313879094694684 * 10 ^ 70 +
        4225575178569581419737987312125762417845645797671760985317704347918509) * 10 ^ 70 +
        1812658736908550105559613916772917302914265047796270341392362958198665) * 10 ^ 70 +
        8901851597606974666637293279167447431607636007115473840812139109611451) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_115 :
    recurrence5B1A3.coeff 115 =
      -((((229803664757689476 * 10 ^ 70 +
        1668618784413633148850822440143912037039081602221403144414536465418845) * 10 ^ 70 +
        6945740079564378864669885047241794452401981707729846423018042215546250) * 10 ^ 70 +
        8204030345970559351060573023156347144927093500011977012078793552946530) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_116 :
    recurrence5B1A3.coeff 116 =
      ((((462270153898985568 * 10 ^ 70 +
        5720011692475793234194453048210328235435628709390720706345649391956535) * 10 ^ 70 +
        7372477583439638892691670584429270135990854403513068987675038446214625) * 10 ^ 70 +
        7835025131779127757839106494199580374644837016332726820539693398901606) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_117 :
    recurrence5B1A3.coeff 117 =
      -((((906132884641168452 * 10 ^ 70 +
        3195931967411118228086846852272073126813012205907857046213594882643256) * 10 ^ 70 +
        3959150888961850565674358459050707788437509619283559214468361244700710) * 10 ^ 70 +
        8486990199558089320005962277500300252820890727522047244269724047537501) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_118 :
    recurrence5B1A3.coeff 118 =
      ((((1730880333520674344 * 10 ^ 70 +
        6757801695263960620475798265939987102807545510351248818989896181433287) * 10 ^ 70 +
        4246118173249056664140804530741288021908418113773712172160768749982078) * 10 ^ 70 +
        3494518885198321494688560460903432948055590852259137617425949407206736) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_119 :
    recurrence5B1A3.coeff 119 =
      -((((3222101660118811915 * 10 ^ 70 +
        8407177923953419166191155246454074837537884441269139747025102462848930) * 10 ^ 70 +
        3994766806928157879150268913834477963756695545155884622197867678387620) * 10 ^ 70 +
        1820368313878818160089127078365548504577036315403894134575775050343286) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_120 :
    recurrence5B1A3.coeff 120 =
      ((((5845506400938865747 * 10 ^ 70 +
        6513660998880034980635149084749798174289591177010629707612888641154437) * 10 ^ 70 +
        1825076144631376893071846130232269613744035408973253176109526731416223) * 10 ^ 70 +
        7041254805968089188268954662198826696482597675902338582658004022402278) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_121 :
    recurrence5B1A3.coeff 121 =
      -((((10335342721377850998 * 10 ^ 70 +
        5035154702534862572923991896111619582240492552520556950728222000286842) * 10 ^ 70 +
        8483265232140750003333137755623540326132083213167695977594682257133256) * 10 ^ 70 +
        3918765460260986930708961569827538481615188106270324870171012736765786) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_122 :
    recurrence5B1A3.coeff 122 =
      ((((17809500887309972773 * 10 ^ 70 +
        0389537295589012124768544618132760749961740344933447663722581336937568) * 10 ^ 70 +
        7387373647853664956362895583078879890637156871615970982046496090811442) * 10 ^ 70 +
        2530558322819145636410410882102518046683154865010155560392793247892800) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_123 :
    recurrence5B1A3.coeff 123 =
      -((((29908992374299325751 * 10 ^ 70 +
        3239743640880328259124141046919891436565252014648307913426074074578669) * 10 ^ 70 +
        0500752680102770679157157809191766578770308602564865165739952184761001) * 10 ^ 70 +
        5173153221975314055056498604882195929958180367505236950583391464066971) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_124 :
    recurrence5B1A3.coeff 124 =
      ((((48951760269600012349 * 10 ^ 70 +
        5874292031210545949279580903183675682565133935479537407191653392981596) * 10 ^ 70 +
        0189780706625666451904790599280570945487105744640210113292995962827063) * 10 ^ 70 +
        3044280728043999258952540598961769158231287532380023765075282888744220) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_125 :
    recurrence5B1A3.coeff 125 =
      -((((78079744847778631115 * 10 ^ 70 +
        5821830394698950312050733849783578984864801402317684683670387043125693) * 10 ^ 70 +
        8678422786636027772065327009531877573100628460324585006465897741623155) * 10 ^ 70 +
        3869665026403211982307883206550595543515982581399848335593776420680104) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_126 :
    recurrence5B1A3.coeff 126 =
      ((((121364607585998657837 * 10 ^ 70 +
        5958862001490954440904388510258798462711746816330232989441514068214060) * 10 ^ 70 +
        6492624315705155760783140295148204192089193265008489113014575291529511) * 10 ^ 70 +
        3225437658990032415234113899180482050050897165104763880945732695932851) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_127 :
    recurrence5B1A3.coeff 127 =
      -((((183823717773467894923 * 10 ^ 70 +
        3393688469398932450897173900274709046814366899001066530203793551170051) * 10 ^ 70 +
        2427014054569189786508244642928304445474122346729439349744259918139416) * 10 ^ 70 +
        9864177069980175360268080945421040134115832813200432507692270330353257) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_128 :
    recurrence5B1A3.coeff 128 =
      ((((271287755121519960626 * 10 ^ 70 +
        7342764257172210909155037617179723803734311036353976017045333411142195) * 10 ^ 70 +
        0014823386406181447120381954121303543200563069105296447692663711249960) * 10 ^ 70 +
        0400413975950091750675222164503737787594433856699066148951689852516812) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_129 :
    recurrence5B1A3.coeff 129 =
      -((((390059772774559461023 * 10 ^ 70 +
        5071872746750954249240076329609452001809903077933333952812289931814916) * 10 ^ 70 +
        0354359117772907676365080030134145249375540393881227691726586782779228) * 10 ^ 70 +
        5349127910595413846839138251518236869443121607370604695683654974388376) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_130 :
    recurrence5B1A3.coeff 130 =
      ((((546318435729620505400 * 10 ^ 70 +
        3724998613128822706658276597349097648684690615869368398454775569087079) * 10 ^ 70 +
        1091922735999417772010410869884767475042856611144822276194488230895768) * 10 ^ 70 +
        6834501271251049910351418894784708512048559288470785262920882870979977) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_131 :
    recurrence5B1A3.coeff 131 =
      -((((745249834384894173271 * 10 ^ 70 +
        2472806428589243535725012552077609466662253902652287164645055547166483) * 10 ^ 70 +
        4190395134111322859582954416623939869087995198686165442345050806466492) * 10 ^ 70 +
        6023301237138156344832794525063443157375180949121996224705649965079815) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_132 :
    recurrence5B1A3.coeff 132 =
      ((((989943849148034203165 * 10 ^ 70 +
        4423451444075916750793927011747503704641602577292229580898463474069650) * 10 ^ 70 +
        6791104705765759050631915693709737980334693385708021615084810088702608) * 10 ^ 70 +
        3599819620639341499624794696106787928730335229377186286559995126460575) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_133 :
    recurrence5B1A3.coeff 133 =
      -((((1280158126502989283134 * 10 ^ 70 +
        1726888523800262021938978216671146409967984516089545653377201802741562) * 10 ^ 70 +
        4252597530908789726321119261855249996993419485583698616329627876487725) * 10 ^ 70 +
        1921004841600522252281860752275785332834681359589926373579962214089569) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_134 :
    recurrence5B1A3.coeff 134 =
      ((((1611124254425567643514 * 10 ^ 70 +
        0346469575680168794347845754984212683221562481363654312796389289755080) * 10 ^ 70 +
        4003224139736643245736126531983779168641116414090546428061806718199555) * 10 ^ 70 +
        1216349503894157942067511922700780695403973329847321360302201111930312) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_135 :
    recurrence5B1A3.coeff 135 =
      -((((1972629497573415750960 * 10 ^ 70 +
        0244341727301535940580371818056161420435576364032844111716695232966589) * 10 ^ 70 +
        1389605678092831028728272466462472190269685793709666736788776859291385) * 10 ^ 70 +
        4158681345864962325579206561964824377778286188347956537332303010600655) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_136 :
    recurrence5B1A3.coeff 136 =
      ((((2348633050168285183677 * 10 ^ 70 +
        8117451808024821331180575771159473556226133097842950729809396289466187) * 10 ^ 70 +
        6947554741506310901642883003208319100510057106429475138043104366792607) * 10 ^ 70 +
        5822247759172530530787376644668523431706327224117656670150946211961004) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_137 :
    recurrence5B1A3.coeff 137 =
      -((((2717649726443993347434 * 10 ^ 70 +
        1515573334363795861255852385271253010778850342004540928174172323824777) * 10 ^ 70 +
        9373328737736251789784852363978070837816168718661388378972827433376923) * 10 ^ 70 +
        1019846845878413242277020683178924864478493689433185050271455166319524) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_138 :
    recurrence5B1A3.coeff 138 =
      ((((3054046270775505497919 * 10 ^ 70 +
        1318441712448865336851405874885812432417836093987697507437109386261256) * 10 ^ 70 +
        9627566182456178193647452896797907442889232210586558435232956250214752) * 10 ^ 70 +
        7387092921513363276124428699794725954326795150657836717180591289689992) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_139 :
    recurrence5B1A3.coeff 139 =
      -((((3330250179936225517783 * 10 ^ 70 +
        8763004371543385488050424444742130933103256158505566054450109340087802) * 10 ^ 70 +
        9087615377683021990978519871921179156921717425352170369198614608277250) * 10 ^ 70 +
        7842243468436521550757827665598622806751320845366594104687644983536403) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_140 :
    recurrence5B1A3.coeff 140 =
      ((((3519689370485187054435 * 10 ^ 70 +
        4432602002262252154898692212117007298523293139962039305059375074918047) * 10 ^ 70 +
        6790585125319774591609272371495414156770585047501515795787050811361305) * 10 ^ 70 +
        3035636838716140799102387077978297015043319544787826016798144626484252) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_141 :
    recurrence5B1A3.coeff 141 =
      -((((3600099762236623198376 * 10 ^ 70 +
        6534571386600595380908059356992907505936113522918217864304949238063961) * 10 ^ 70 +
        9896745054917929476136720192272616166032614966648419260414009575095069) * 10 ^ 70 +
        1752943795295242863510056035617752412811417487616390868069321153574969) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_142 :
    recurrence5B1A3.coeff 142 =
      ((((3556701495990147550057 * 10 ^ 70 +
        5680367418722054912216464244698213717306105251263467761403452731699698) * 10 ^ 70 +
        0026976130672103878793278796631138347778153340040335775303596402020712) * 10 ^ 70 +
        5848164561698402787130881874449072211050574263679935494656221375556425) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_143 :
    recurrence5B1A3.coeff 143 =
      -((((3384694301551762836723 * 10 ^ 70 +
        4567049769922282952521000258621897674085516170814701758445283334816275) * 10 ^ 70 +
        5941363747889741683532780140053724485209526483472171711459191139541688) * 10 ^ 70 +
        6501660788342600050972515678346600057300147009546621341857260288049250) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_144 :
    recurrence5B1A3.coeff 144 =
      ((((3090583771640835470501 * 10 ^ 70 +
        8316424717687908245546049307448572597862523675228644573866260532377944) * 10 ^ 70 +
        8750511790874227734430881624703257066403092219399795929581676133847779) * 10 ^ 70 +
        1256509104241441492232960117212073453017017267820719942483390755039508) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_145 :
    recurrence5B1A3.coeff 145 =
      -((((2692022593218959453998 * 10 ^ 70 +
        4748822075571308564213074927054545764823354973474979343890055301967263) * 10 ^ 70 +
        5500973950806113521136735598839085827551088064216606310680346333106782) * 10 ^ 70 +
        0515710178288645788807810765558772609681294029870589188687027240130930) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_146 :
    recurrence5B1A3.coeff 146 =
      ((((2216104882931336144643 * 10 ^ 70 +
        8976694059654915158070403012114179343309106186651066982148453835506915) * 10 ^ 70 +
        8356550929927589729829570492642282556276277230628693777764264380838614) * 10 ^ 70 +
        5736688750375168951848958756053562242400360546720824597428067795720509) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_147 :
    recurrence5B1A3.coeff 147 =
      -((((1696334771169582388970 * 10 ^ 70 +
        1966026530578096573451621291948217449677941882332284933278381720933130) * 10 ^ 70 +
        9243919591624522445580297336580824866442768952776025888404564519382810) * 10 ^ 70 +
        9462935794965288793910172592023300830673960421196233754928336225981228) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_148 :
    recurrence5B1A3.coeff 148 =
      ((((1168738582272903478090 * 10 ^ 70 +
        4652498502575117371892790951102417018151937681722567847710231298491101) * 10 ^ 70 +
        9006151521380294967408270614872638372373519581328691047634978911051955) * 10 ^ 70 +
        8591221023173859750127283027460963237822607476740971460408882332226757) : ℚ) := by
  unfold recurrence5B1A3
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

theorem recurrence5B1A3_coeff_149 :
    recurrence5B1A3.coeff 149 =
      -((((667745789158280733079 * 10 ^ 70 +
        3214060340802266070701496802160247571364853455464027256043551797141089) * 10 ^ 70 +
        6870054493125727036454062553539548247515300326034213902479843825932138) * 10 ^ 70 +
        8573393631876245165870861095721574398632896078157222728545886830199530) : ℚ) := by
  unfold recurrence5B1A3
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

private theorem recurrence5B1A3_coeff_150_suffix_zero :
    (∑ x ∈ Finset.range 1,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (150 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_150 :
    recurrence5B1A3.coeff 150 =
      ((((222491767065150853213 * 10 ^ 70 +
        7433526164715881836425481711855752321169238824993227978851826925340228) * 10 ^ 70 +
        2347948838405077003763798443733052704654820113221596141113061392619105) * 10 ^ 70 +
        2952213231712987160497582705408228128811855809544970054022812561043945) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 23 = 22 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_150_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_151_suffix_zero :
    (∑ x ∈ Finset.range 2,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (151 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_151 :
    recurrence5B1A3.coeff 151 =
      ((((145908669090124038113 * 10 ^ 70 +
        5970908065571126360572764504094977811149645032015104822179628147971453) * 10 ^ 70 +
        2480192702142150412749746872785485102190834908996534419830091531414907) * 10 ^ 70 +
        0333719159030366615699859868176812053175282329293768689653285538341811) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 24 = 22 +
      2 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_151_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_152_suffix_zero :
    (∑ x ∈ Finset.range 3,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (152 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_152 :
    recurrence5B1A3.coeff 152 =
      -((((425775527349951458324 * 10 ^ 70 +
        6358425841630066315278722020211999438419970278666582857040469899499354) * 10 ^ 70 +
        5072592202740952110764364146408480174089781778945791130812223269524299) * 10 ^ 70 +
        9673966935149128498335961638391970632043486279093571444665296879784842) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 25 = 22 +
      3 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_152_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_153_suffix_zero :
    (∑ x ∈ Finset.range 4,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (153 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_153 :
    recurrence5B1A3.coeff 153 =
      ((((614883452156075799937 * 10 ^ 70 +
        9398135728751386699866175149109371537924321999907717596576265664578659) * 10 ^ 70 +
        1637906134231124866479415928118226874003020777776239487027054277135409) * 10 ^ 70 +
        6254504433847372819872356563925617161225889353401283076060376980483011) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 26 = 22 +
      4 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_153_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_154_suffix_zero :
    (∑ x ∈ Finset.range 5,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (154 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_154 :
    recurrence5B1A3.coeff 154 =
      -((((719255060513491107871 * 10 ^ 70 +
        2389719419005281065856239249134001475643454084254298106159077603325420) * 10 ^ 70 +
        9218884039327324530563919817867172038464076117911831102339476485932659) * 10 ^ 70 +
        2665584547015237070743463030860490621844719576368013869651260482952730) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 27 = 22 +
      5 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_154_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_155_suffix_zero :
    (∑ x ∈ Finset.range 6,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (155 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_155 :
    recurrence5B1A3.coeff 155 =
      ((((751084228375487791305 * 10 ^ 70 +
        9011498167860773310004964736274429325868434380614985260593559121800905) * 10 ^ 70 +
        2380519232283868851914245678465605652246085217526612709544424801628184) * 10 ^ 70 +
        5469875499205797880248043314673424806338879656222403446999581258019867) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 28 = 22 +
      6 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_155_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_156_suffix_zero :
    (∑ x ∈ Finset.range 7,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (156 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_156 :
    recurrence5B1A3.coeff 156 =
      -((((726240085150188712872 * 10 ^ 70 +
        3991691443568615061502021127059869137001675634208635855506600276932344) * 10 ^ 70 +
        6557656147404013369324630030653781649321319557903618255556149539610778) * 10 ^ 70 +
        1556284314681060731246840049573484381314270461804295200261805048345989) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 29 = 22 +
      7 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_156_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_157_suffix_zero :
    (∑ x ∈ Finset.range 8,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (157 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_157 :
    recurrence5B1A3.coeff 157 =
      ((((661796488893218280043 * 10 ^ 70 +
        1396324522462921219672092708802797185775409697608741607611196129735669) * 10 ^ 70 +
        8230529849609594992647473275964751527395495550593060106479295799197227) * 10 ^ 70 +
        5737630650028324087983977052411017188976799914925712628154566773680396) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 30 = 22 +
      8 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_157_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_158_suffix_zero :
    (∑ x ∈ Finset.range 9,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (158 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_158 :
    recurrence5B1A3.coeff 158 =
      -((((573943276210988164074 * 10 ^ 70 +
        6182988196831383784374148395060424751188244984246485590614258377119519) * 10 ^ 70 +
        7769457905895964135595380146453528199063180510358881068586575947260364) * 10 ^ 70 +
        4276478694713123552812136533339183782416512264686163194997183826510509) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 31 = 22 +
      9 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_158_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_159_suffix_zero :
    (∑ x ∈ Finset.range 10,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (159 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_159 :
    recurrence5B1A3.coeff 159 =
      ((((476498139052099747503 * 10 ^ 70 +
        3494268883820268266805654773414180117239509610715107911814812909623334) * 10 ^ 70 +
        0868268572571494099121381200096677561537728864304149620803908646939134) * 10 ^ 70 +
        1186834055792559106479006163571029331888718533794683854948754034905868) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 32 = 22 +
      10 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_159_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_160_suffix_zero :
    (∑ x ∈ Finset.range 11,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (160 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_160 :
    recurrence5B1A3.coeff 160 =
      -((((380089717897558270606 * 10 ^ 70 +
        7632347964880164255713327865192823216747563703851520986583628338053947) * 10 ^ 70 +
        9016918485689347319597849567370702979536108397151088853368977261349476) * 10 ^ 70 +
        7371035274421870772219125856428446134039085483830602367214131974068994) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 33 = 22 +
      11 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_160_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_161_suffix_zero :
    (∑ x ∈ Finset.range 12,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (161 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_161 :
    recurrence5B1A3.coeff 161 =
      ((((291955944290318127098 * 10 ^ 70 +
        5394157582988855622576655271557070315286006780967944791681705673182163) * 10 ^ 70 +
        2155776874800761886822490988114916381566872294069518533872914791708190) * 10 ^ 70 +
        7210717800464807780054467317772783320179780284782782554613945236305634) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 34 = 22 +
      12 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_161_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_162_suffix_zero :
    (∑ x ∈ Finset.range 13,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (162 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_162 :
    recurrence5B1A3.coeff 162 =
      -((((216217083886216883956 * 10 ^ 70 +
        5034357348527587712625015063895370320824540104877221235491540237977581) * 10 ^ 70 +
        7937744945856398661413699810496564890192663608033861983540946264676217) * 10 ^ 70 +
        3542625931512077386080401223916046287766088711136231573377420163436068) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 35 = 22 +
      13 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_162_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_163_suffix_zero :
    (∑ x ∈ Finset.range 14,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (163 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_163 :
    recurrence5B1A3.coeff 163 =
      ((((154446369778793258927 * 10 ^ 70 +
        7351373931789465024056698572353461199789165641295607711140300340663371) * 10 ^ 70 +
        9661364819084474714079451408463582246125871637281584815493638487702544) * 10 ^ 70 +
        4128200332183129480673074327376661343706200952583880133263502160094750) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 36 = 22 +
      14 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_163_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_164_suffix_zero :
    (∑ x ∈ Finset.range 15,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (164 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_164 :
    recurrence5B1A3.coeff 164 =
      -((((106366570454688563347 * 10 ^ 70 +
        5698293929213996300484367426723104942838548204851772364971360518155550) * 10 ^ 70 +
        8611268992181425359351051877689806279990144504931986894823843447029871) * 10 ^ 70 +
        2657275583000049560639707240840007657154320103459100339923480282903700) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 37 = 22 +
      15 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_164_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_165_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (165 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_165_suffix_zero :
    (∑ x ∈ Finset.range 16,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (165 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_165 :
    recurrence5B1A3.coeff 165 =
      ((((70534935404509769926 * 10 ^ 70 +
        1749895733086566628265290315516218443315853930973680941365008424942930) * 10 ^ 70 +
        6591945885417979450971907174119883696267035527681145180509881439739126) * 10 ^ 70 +
        7858522256241062776196946741807583654141401222756148217125482908354514) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 37 = 21 +
      16 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_165_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_165_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_166_prefix_zero :
    (∑ x ∈ Finset.range 2,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (166 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (166 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_166_suffix_zero :
    (∑ x ∈ Finset.range 17,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (166 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_166 :
    recurrence5B1A3.coeff 166 =
      -((((44926210233912653911 * 10 ^ 70 +
        9840661468183852006150807815696686400450959436286740302934304189149670) * 10 ^ 70 +
        1761356867441426632938082420263056568648742595609678500997248977314923) * 10 ^ 70 +
        2978077536204277768556638380230954868539603492017820171307715783823358) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 37 = 20 +
      17 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_166_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_166_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_167_prefix_zero :
    (∑ x ∈ Finset.range 3,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (167 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (167 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_167_suffix_zero :
    (∑ x ∈ Finset.range 18,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (167 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_167 :
    recurrence5B1A3.coeff 167 =
      ((((27370428250093689509 * 10 ^ 70 +
        1608651914686331557036879568458539328994735311846150107942992372518036) * 10 ^ 70 +
        5517716327525965657831326146956438287036820955523847886240795651638580) * 10 ^ 70 +
        1708666270000865775280294685576589071720191948405787102976616848461338) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 37 = 19 +
      18 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_167_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_167_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_168_prefix_zero :
    (∑ x ∈ Finset.range 4,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (168 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (168 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_168_suffix_zero :
    (∑ x ∈ Finset.range 19,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (168 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_168 :
    recurrence5B1A3.coeff 168 =
      -((((15840082331275603799 * 10 ^ 70 +
        9872307400694260491256304426707859541706391688038259092766230497936479) * 10 ^ 70 +
        5791372681228879572074905851629197423899096113612695289867901167511259) * 10 ^ 70 +
        4324677928446408580524356779250480507413461374945374100575761443558926) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 37 = 18 +
      19 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_168_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_168_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_169_prefix_zero :
    (∑ x ∈ Finset.range 5,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (169 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (169 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_169_suffix_zero :
    (∑ x ∈ Finset.range 20,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (169 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_169 :
    recurrence5B1A3.coeff 169 =
      ((((8606170082079437933 * 10 ^ 70 +
        3456246498257957630862838972674033801129346905514590285625252801721087) * 10 ^ 70 +
        3424233254357222853931394507379714640206859597058242116129871821507498) * 10 ^ 70 +
        8278770303821290148331950985078398138426612705936625778236328639090094) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 37 = 17 +
      20 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_169_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_169_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_170_prefix_zero :
    (∑ x ∈ Finset.range 6,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (170 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (170 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_170_suffix_zero :
    (∑ x ∈ Finset.range 21,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (170 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_170 :
    recurrence5B1A3.coeff 170 =
      -((((4294696525852669412 * 10 ^ 70 +
        3895683051944630971329282520832571340751774248176622833576294714129955) * 10 ^ 70 +
        2653497232849493457378734232815736547587375924444993648268696293033913) * 10 ^ 70 +
        5545311679296657711080613386354551622771113346173596901236924181578010) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 37 = 16 +
      21 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_170_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_170_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_171_prefix_zero :
    (∑ x ∈ Finset.range 7,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (171 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (171 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_171_suffix_zero :
    (∑ x ∈ Finset.range 22,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (171 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_171 :
    recurrence5B1A3.coeff 171 =
      ((((1877253568224390693 * 10 ^ 70 +
        7097489974733632601368165383952883373347652617317285196734059922877655) * 10 ^ 70 +
        6872348725957690625088558456983313975924057031144519437389703915845077) * 10 ^ 70 +
        3220309396611500067276999633931969818601457174919472165142423472239822) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 37 = 15 +
      22 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_171_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_171_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_172_prefix_zero :
    (∑ x ∈ Finset.range 8,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (172 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (172 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_172_suffix_zero :
    (∑ x ∈ Finset.range 23,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (172 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_172 :
    recurrence5B1A3.coeff 172 =
      -((((624962138034567365 * 10 ^ 70 +
        6523496045510611751089839921680772869577669896601639291968178209937424) * 10 ^ 70 +
        1617382231159466913269842933720140283829326233787704829345643731958339) * 10 ^ 70 +
        3071194281482349709968690435120853787999462997791511720808929477595937) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 37 = 14 +
      23 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_172_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_172_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_173_prefix_zero :
    (∑ x ∈ Finset.range 9,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (173 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (173 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_173_suffix_zero :
    (∑ x ∈ Finset.range 24,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (173 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_173 :
    recurrence5B1A3.coeff 173 =
      ((((47806583694716461 * 10 ^ 70 +
        4101286304064084668604474230954252447940909047329276137574682303306118) * 10 ^ 70 +
        9315906507721099002595145055740300672106861695265211850755028653904327) * 10 ^ 70 +
        2545487616381492592279272223795313612136682069397858960694769597355316) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 37 = 13 +
      24 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_173_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_173_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_174_prefix_zero :
    (∑ x ∈ Finset.range 10,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (174 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (174 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_174_suffix_zero :
    (∑ x ∈ Finset.range 25,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (174 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_174 :
    recurrence5B1A3.coeff 174 =
      ((((166231855393716302 * 10 ^ 70 +
        4847061613652383040251795294299872242187071493992639217243177129583952) * 10 ^ 70 +
        3792308684789185265201505496250395578258440316472453918879757538797872) * 10 ^ 70 +
        0032929638595729566087026585223128966917274080736213004137658785502095) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 37 = 12 +
      25 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_174_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_174_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_175_prefix_zero :
    (∑ x ∈ Finset.range 11,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (175 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (175 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_175_suffix_zero :
    (∑ x ∈ Finset.range 26,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (175 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_175 :
    recurrence5B1A3.coeff 175 =
      -((((204320984450881800 * 10 ^ 70 +
        7512537374960658187825489096316496989314346642467256506512553697880710) * 10 ^ 70 +
        4036886693725967690613692755660899955575118813424913126166268587833810) * 10 ^ 70 +
        8864353592758423667910713477532379400877785382246912314225359597952425) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 37 = 11 +
      26 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_175_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_175_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_176_prefix_zero :
    (∑ x ∈ Finset.range 12,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (176 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (176 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_176_suffix_zero :
    (∑ x ∈ Finset.range 27,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (176 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_176 :
    recurrence5B1A3.coeff 176 =
      ((((171025722892021524 * 10 ^ 70 +
        4418287877948373971152407410066648837140512080349524326168787379866815) * 10 ^ 70 +
        6999756914202845919743247017022644902005203839746671733566736299227582) * 10 ^ 70 +
        0389498369819292272338479136246812400741268079885464536826176516545971) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 37 = 10 +
      27 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_176_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_176_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_177_prefix_zero :
    (∑ x ∈ Finset.range 13,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (177 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (177 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_177_suffix_zero :
    (∑ x ∈ Finset.range 28,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (177 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_177 :
    recurrence5B1A3.coeff 177 =
      -((((119491122106760021 * 10 ^ 70 +
        6640513418778050195603354980581318254690198505448474605337578363901212) * 10 ^ 70 +
        3177375871659159030087392460376395903307638154094828498210695906143177) * 10 ^ 70 +
        2739598967587491399846186603447433510405029246230593573474975820513458) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 37 = 9 +
      28 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_177_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_177_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_178_prefix_zero :
    (∑ x ∈ Finset.range 14,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (178 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (178 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_178_suffix_zero :
    (∑ x ∈ Finset.range 29,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (178 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_178 :
    recurrence5B1A3.coeff 178 =
      ((((72994432450766246 * 10 ^ 70 +
        8904225233977728789133613688292263713080568538560266850174750648321187) * 10 ^ 70 +
        5373258735275803595441948130937862022713725271008014183668840894719760) * 10 ^ 70 +
        6432493069213463487257484545887129531816407622891299580938006036084376) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 37 = 8 +
      29 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_178_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_178_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_179_prefix_zero :
    (∑ x ∈ Finset.range 15,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (179 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (179 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_179_suffix_zero :
    (∑ x ∈ Finset.range 30,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (179 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_179 :
    recurrence5B1A3.coeff 179 =
      -((((38915046181994298 * 10 ^ 70 +
        1402521324058696133797529588269382942447737648972394433601727488937925) * 10 ^ 70 +
        8922854938573624905768807965824657272043836119013347151476990088213290) * 10 ^ 70 +
        7159561123992166917075321795065841284260228275541837103564814613097471) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 37 = 7 +
      30 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_179_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_179_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_180_prefix_zero :
    (∑ x ∈ Finset.range 16,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (180 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (180 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_180_suffix_zero :
    (∑ x ∈ Finset.range 31,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (180 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_180 :
    recurrence5B1A3.coeff 180 =
      ((((17186329052556079 * 10 ^ 70 +
        8182021616738886491312416010810247420382433759052379907703427578942976) * 10 ^ 70 +
        1401741935189178577431366110690351700975185362388852135057204001960827) * 10 ^ 70 +
        9195942560022634829991675123276423404097903297244974040805990456224379) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 37 = 6 +
      31 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_180_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_180_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_181_prefix_zero :
    (∑ x ∈ Finset.range 17,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (181 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (181 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_181_suffix_zero :
    (∑ x ∈ Finset.range 32,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (181 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_181 :
    recurrence5B1A3.coeff 181 =
      -((((5004230123704493 * 10 ^ 70 +
        0709285160979995156419520967892630457404284118640480321006067692240713) * 10 ^ 70 +
        5169017695777774407697638103964894474880141041402397003499809131642179) * 10 ^ 70 +
        2351210960488379455186457147570775557769851236925913272887524755494965) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 37 = 5 +
      32 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_181_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_181_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_182_prefix_zero :
    (∑ x ∈ Finset.range 18,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (182 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (182 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_182_suffix_zero :
    (∑ x ∈ Finset.range 33,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (182 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_182 :
    recurrence5B1A3.coeff 182 =
      -((((829851837774744 * 10 ^ 70 +
        9741666212108834321057213380816392540075525918898340238650269807429474) * 10 ^ 70 +
        5961694463209292250426915267926457719844974809419111689341784213302360) * 10 ^ 70 +
        4593146947769372167375428600382945536833927555348874183818215131436595) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 37 = 4 +
      33 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_182_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_182_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_183_prefix_zero :
    (∑ x ∈ Finset.range 19,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (183 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (183 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_183_suffix_zero :
    (∑ x ∈ Finset.range 34,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (183 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_183 :
    recurrence5B1A3.coeff 183 =
      ((((2946538079547601 * 10 ^ 70 +
        8571534215730870232310464961064504973214675850090951616991956185971015) * 10 ^ 70 +
        2985100818364682212738159700122739745880382183531244112036685069510034) * 10 ^ 70 +
        5527011092804275071142197311768689933015754779663205909949488528567114) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 37 = 3 +
      34 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_183_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_183_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_184_prefix_zero :
    (∑ x ∈ Finset.range 20,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (184 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (184 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_184_suffix_zero :
    (∑ x ∈ Finset.range 35,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (184 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_184 :
    recurrence5B1A3.coeff 184 =
      -((((3172591669950470 * 10 ^ 70 +
        3117848169261494798353356916486739123748733135827238134365795456001274) * 10 ^ 70 +
        4024229980423821147446948768939578893263184663804797363974949577025814) * 10 ^ 70 +
        4544916761693237964402363004850624024107076442551175421767562095715774) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 37 = 2 +
      35 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_184_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_184_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_185_prefix_zero :
    (∑ x ∈ Finset.range 21,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (185 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (185 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_185_suffix_zero :
    (∑ x ∈ Finset.range 36,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (185 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_185 :
    recurrence5B1A3.coeff 185 =
      ((((2621383613296346 * 10 ^ 70 +
        8781073551209731810679929409237878531690981457957746368798145741638424) * 10 ^ 70 +
        7130748609238725168858905521779363818954798838442021429076002589109228) * 10 ^ 70 +
        0323675767094156735014036061534654877507548613961146890639932043327589) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 37 = 1 +
      36 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_185_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_185_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_186_prefix_zero :
    (∑ x ∈ Finset.range 22,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (186 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (186 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_186_suffix_zero :
    (∑ x ∈ Finset.range 37,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (186 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_186 :
    recurrence5B1A3.coeff 186 =
      -((((1887171857404294 * 10 ^ 70 +
        0931911352196016422908787924834950597444092475119787234918267600202328) * 10 ^ 70 +
        8493047673190939274910351570194789860642081461990711258455485488547967) * 10 ^ 70 +
        6151762300291903139560878929101501394810066048628203285538828418157449) : ℚ) := by
  unfold recurrence5B1A3
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
  rw [recurrence5B1A3_coeff_186_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_186_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_187_prefix_zero :
    (∑ x ∈ Finset.range 23,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (187 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (187 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_187_suffix_zero :
    (∑ x ∈ Finset.range 38,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (187 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_187 :
    recurrence5B1A3.coeff 187 =
      ((((1235412132012376 * 10 ^ 70 +
        2555563888233247413025374429569548601497250915271488522123071137006562) * 10 ^ 70 +
        4066929186949037322117212937288759207670784113706921523058481647719162) * 10 ^ 70 +
        6996002436330733963264237931071747300879406937121372321532417334022480) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 69 = 31 +
      38 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_187_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_187_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_188_prefix_zero :
    (∑ x ∈ Finset.range 24,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (188 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (188 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_188_suffix_zero :
    (∑ x ∈ Finset.range 39,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (188 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_188 :
    recurrence5B1A3.coeff 188 =
      -((((748696731855336 * 10 ^ 70 +
        0486606207628409066254395736746351236023678698564299235490255241674132) * 10 ^ 70 +
        0909338820213000186556474152262090225773257993130058025209417181838912) * 10 ^ 70 +
        4264056296064662189191608241060553093141651885874929471271553497973066) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 69 = 30 +
      39 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_188_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_188_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_189_prefix_zero :
    (∑ x ∈ Finset.range 25,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (189 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (189 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_189_suffix_zero :
    (∑ x ∈ Finset.range 40,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (189 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_189 :
    recurrence5B1A3.coeff 189 =
      ((((422825305877086 * 10 ^ 70 +
        3519185704377583867568448620935708545939899239571648014804907625187904) * 10 ^ 70 +
        9169836865984658429206537641955046439237212791648950714210347147004740) * 10 ^ 70 +
        0470572064581151257910552748873882425279213954326782187641906021266229) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 69 = 29 +
      40 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_189_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_189_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_190_prefix_zero :
    (∑ x ∈ Finset.range 26,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (190 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (190 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_190_suffix_zero :
    (∑ x ∈ Finset.range 41,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (190 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_190 :
    recurrence5B1A3.coeff 190 =
      -((((222229740744681 * 10 ^ 70 +
        2253480997395341638415843587555543183511919162069991231176880392894533) * 10 ^ 70 +
        4823033426174026435445318445979140957933343698321347386286122978935165) * 10 ^ 70 +
        6959041041792331820486517308192123663131890679963738918856011017613911) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 69 = 28 +
      41 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_190_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_190_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_191_prefix_zero :
    (∑ x ∈ Finset.range 27,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (191 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (191 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_191_suffix_zero :
    (∑ x ∈ Finset.range 42,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (191 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_191 :
    recurrence5B1A3.coeff 191 =
      ((((107552472377463 * 10 ^ 70 +
        6602247201734166220241145215369825578262419966262754569733473317838368) * 10 ^ 70 +
        9136994020176901661294883521012983543484357388129835429231133057359544) * 10 ^ 70 +
        7466169135345708378890484148024810779206553276349096908817478172612229) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 69 = 27 +
      42 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_191_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_191_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_192_prefix_zero :
    (∑ x ∈ Finset.range 28,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (192 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (192 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_192_suffix_zero :
    (∑ x ∈ Finset.range 43,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (192 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_192 :
    recurrence5B1A3.coeff 192 =
      -((((46606450430257 * 10 ^ 70 +
        0456844321509393360567145812862427459816622015845000229310752810824835) * 10 ^ 70 +
        4173802211862737196382950516622449126191953917835299588592230130126274) * 10 ^ 70 +
        8621625054562789528509426334325685787425430004209793044022347567881176) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 69 = 26 +
      43 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_192_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_192_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_193_prefix_zero :
    (∑ x ∈ Finset.range 29,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (193 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (193 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_193_suffix_zero :
    (∑ x ∈ Finset.range 44,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (193 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_193 :
    recurrence5B1A3.coeff 193 =
      ((((16742386760387 * 10 ^ 70 +
        6623260712028782546722332134196918591378209828961649043404801115809848) * 10 ^ 70 +
        4662605462728452840486516023006610079913128395930849788970852674289665) * 10 ^ 70 +
        4805912896633660437112948966073948045025359611846427144277940217379568) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 69 = 25 +
      44 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_193_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_193_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_194_prefix_zero :
    (∑ x ∈ Finset.range 30,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (194 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (194 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_194_suffix_zero :
    (∑ x ∈ Finset.range 45,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (194 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_194 :
    recurrence5B1A3.coeff 194 =
      -((((3568930129904 * 10 ^ 70 +
        1065297006426968911923491700488599011707087216948333128718073285438145) * 10 ^ 70 +
        5739038902233538676682236846271119735828133321385335691535034118548973) * 10 ^ 70 +
        4631533997043068430736523952176621060328585249498308584513635282414862) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 69 = 24 +
      45 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_194_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_194_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_195_prefix_zero :
    (∑ x ∈ Finset.range 31,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (195 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (195 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_195_suffix_zero :
    (∑ x ∈ Finset.range 46,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (195 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_195 :
    recurrence5B1A3.coeff 195 =
      -((((1333547296810 * 10 ^ 70 +
        2216305558486899146392464377441179985974294823536595952796049491704330) * 10 ^ 70 +
        5204591863562158963313542386988232569804294301857263441855844766998820) * 10 ^ 70 +
        6653122931166873624224158340259947558725365835201298024762289844821909) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 69 = 23 +
      46 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_195_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_195_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_196_prefix_zero :
    (∑ x ∈ Finset.range 32,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (196 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (196 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_196_suffix_zero :
    (∑ x ∈ Finset.range 47,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (196 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_196 :
    recurrence5B1A3.coeff 196 =
      ((((2529770858323 * 10 ^ 70 +
        3991846018269387864685888735024711478510602111334144104028652711276834) * 10 ^ 70 +
        1537661530406075109807856986463839392047593285314454766033856505157249) * 10 ^ 70 +
        8551595564773514943150020935025645944600954872603541482564866368500349) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 69 = 22 +
      47 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_196_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_196_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_197_prefix_zero :
    (∑ x ∈ Finset.range 33,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (197 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (197 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_197_suffix_zero :
    (∑ x ∈ Finset.range 48,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (197 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_197 :
    recurrence5B1A3.coeff 197 =
      -((((2304965858753 * 10 ^ 70 +
        2677058927590319329646105272622864060280333153859424376486219340695701) * 10 ^ 70 +
        5801231657780276148139482443439712902433547228618599283386464382980735) * 10 ^ 70 +
        7576614802840951231231338880183659349267276068337252921183431444086091) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 69 = 21 +
      48 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_197_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_197_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_198_prefix_zero :
    (∑ x ∈ Finset.range 34,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (198 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (198 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_198_suffix_zero :
    (∑ x ∈ Finset.range 49,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (198 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_198 :
    recurrence5B1A3.coeff 198 =
      ((((1697646554394 * 10 ^ 70 +
        2032209954997916685285323156479072224858634970257874339572368399589805) * 10 ^ 70 +
        6925305507251209957381879046683276073597066325766748168519794460481935) * 10 ^ 70 +
        7565771053707463287212019480590706036012791571371480231649652576624915) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 69 = 20 +
      49 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_198_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_198_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_199_prefix_zero :
    (∑ x ∈ Finset.range 35,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (199 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (199 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_199_suffix_zero :
    (∑ x ∈ Finset.range 50,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (199 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_199 :
    recurrence5B1A3.coeff 199 =
      -((((1116377313102 * 10 ^ 70 +
        8420355740900661889566800591895212748325652513580875918620440474882640) * 10 ^ 70 +
        0259714484143456839074677500539711414601778883523873964540868294741728) * 10 ^ 70 +
        2541935240834607829598250917137458564423206110891246393937907065545389) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 69 = 19 +
      50 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_199_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_199_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_200_prefix_zero :
    (∑ x ∈ Finset.range 36,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (200 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (200 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_200_suffix_zero :
    (∑ x ∈ Finset.range 51,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (200 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_200 :
    recurrence5B1A3.coeff 200 =
      ((((679767278873 * 10 ^ 70 +
        8648215487895280297808510023085974048733903463415736239181041463608486) * 10 ^ 70 +
        1537380300299218648046191192902181524591328892605269487941292788942818) * 10 ^ 70 +
        6323652081702439490088518861912173992421571914594463499760044249620063) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 69 = 18 +
      51 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_200_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_200_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_201_prefix_zero :
    (∑ x ∈ Finset.range 37,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (201 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (201 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_201_suffix_zero :
    (∑ x ∈ Finset.range 52,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (201 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_201 :
    recurrence5B1A3.coeff 201 =
      -((((389725248462 * 10 ^ 70 +
        8558417394915663132269896035300230952890739277026546543632851803258402) * 10 ^ 70 +
        9478403886091046361030048377874796622736559918480966017024526107241348) * 10 ^ 70 +
        3998604578510787326085015178137707339285632630633665691212507764794302) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 69 = 17 +
      52 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_201_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_201_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_202_prefix_zero :
    (∑ x ∈ Finset.range 38,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (202 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (202 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_202_suffix_zero :
    (∑ x ∈ Finset.range 53,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (202 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_202 :
    recurrence5B1A3.coeff 202 =
      ((((212154418763 * 10 ^ 70 +
        7804424256375848388738927977913339617585869769049884057395329953433419) * 10 ^ 70 +
        4299578897460946657485598985741495911093559463618574770836555462044105) * 10 ^ 70 +
        5563797137564573992329345829246825795929329569478371685906908270413776) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 69 = 16 +
      53 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_202_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_202_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_203_prefix_zero :
    (∑ x ∈ Finset.range 39,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (203 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (203 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_203_suffix_zero :
    (∑ x ∈ Finset.range 54,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (203 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_203 :
    recurrence5B1A3.coeff 203 =
      -((((110111236024 * 10 ^ 70 +
        8988784018832301300441820823051185894631096471786290786991942922622019) * 10 ^ 70 +
        7071578226540123125623985269664034011509241499030945694007422822956294) * 10 ^ 70 +
        3578402077751291555727661065894815315764010741193879509274439243365660) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 69 = 15 +
      54 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_203_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_203_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_204_prefix_zero :
    (∑ x ∈ Finset.range 40,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (204 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (204 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_204_suffix_zero :
    (∑ x ∈ Finset.range 55,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (204 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_204 :
    recurrence5B1A3.coeff 204 =
      ((((54572852897 * 10 ^ 70 +
        8578908346250739957737607651832341858875629635312563417396973118796284) * 10 ^ 70 +
        2060268933698258458333030335547640611743017905843939103148494650494903) * 10 ^ 70 +
        0191918819248137013658158425597695392742159031212001340651888798144104) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 69 = 14 +
      55 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_204_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_204_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_205_prefix_zero :
    (∑ x ∈ Finset.range 41,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (205 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (205 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_205_suffix_zero :
    (∑ x ∈ Finset.range 56,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (205 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_205 :
    recurrence5B1A3.coeff 205 =
      -((((25821654441 * 10 ^ 70 +
        8155186010385139644844567201366017076595103311423546883694464988973882) * 10 ^ 70 +
        8100781927035281062987285433322905031471291157564319623448037228364624) * 10 ^ 70 +
        6661260502410617490441244349715174669515247355482675384662086118173788) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 69 = 13 +
      56 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_205_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_205_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_206_prefix_zero :
    (∑ x ∈ Finset.range 42,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (206 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (206 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_206_suffix_zero :
    (∑ x ∈ Finset.range 57,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (206 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_206 :
    recurrence5B1A3.coeff 206 =
      ((((11643438502 * 10 ^ 70 +
        9961377340920586411927444420664077116433370739592159700617960828458275) * 10 ^ 70 +
        5666441157685412409711130500151390042895916519666964370334696793016174) * 10 ^ 70 +
        7157068832754152017845244954436222336939494210634043394397089515158908) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 69 = 12 +
      57 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_206_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_206_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_207_prefix_zero :
    (∑ x ∈ Finset.range 43,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (207 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (207 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_207_suffix_zero :
    (∑ x ∈ Finset.range 58,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (207 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_207 :
    recurrence5B1A3.coeff 207 =
      -((((4986327634 * 10 ^ 70 +
        1702527065842475973354232269621562616995053016910181878739572577071752) * 10 ^ 70 +
        6433998375580226983483926668695394432385370304210025259300031286013684) * 10 ^ 70 +
        8980838355552498279853346672808111387222163017797870033304037292216582) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 69 = 11 +
      58 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_207_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_207_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_208_prefix_zero :
    (∑ x ∈ Finset.range 44,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (208 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (208 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_208_suffix_zero :
    (∑ x ∈ Finset.range 59,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (208 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_208 :
    recurrence5B1A3.coeff 208 =
      ((((2016751701 * 10 ^ 70 +
        2178418428828565547347595843990256980503173717245865072322027514923625) * 10 ^ 70 +
        1236588640991712635418375259586079303909091891161471923441225074245792) * 10 ^ 70 +
        7265265163514030305685426556476468182038830934849421706190294844242350) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 69 = 10 +
      59 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_208_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_208_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_209_prefix_zero :
    (∑ x ∈ Finset.range 45,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (209 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (209 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_209_suffix_zero :
    (∑ x ∈ Finset.range 60,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (209 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_209 :
    recurrence5B1A3.coeff 209 =
      -((((763448485 * 10 ^ 70 +
        3086207580169140902575806387481179727443434073319832386993911194951860) * 10 ^ 70 +
        0403029516977474598080311938671728230743586505225714037206436177851154) * 10 ^ 70 +
        1290784094002481573710865460093776032063672840648463053756710745985018) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 69 = 9 +
      60 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_209_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_209_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_210_prefix_zero :
    (∑ x ∈ Finset.range 46,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (210 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (210 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_210_suffix_zero :
    (∑ x ∈ Finset.range 61,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (210 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_210 :
    recurrence5B1A3.coeff 210 =
      ((((266381632 * 10 ^ 70 +
        2883601699803619232280385893110904424343187164137131736083369722858537) * 10 ^ 70 +
        8098114128377826264987808525925944697496316828082925251435867323558671) * 10 ^ 70 +
        8113547118028783060586430630659794177392201918234735600867210808077250) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 69 = 8 +
      61 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_210_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_210_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_211_prefix_zero :
    (∑ x ∈ Finset.range 47,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (211 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (211 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_211_suffix_zero :
    (∑ x ∈ Finset.range 62,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (211 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_211 :
    recurrence5B1A3.coeff 211 =
      -((((83204665 * 10 ^ 70 +
        1718606093450564055588283071481128692328769085309022351459103220391020) * 10 ^ 70 +
        1517764067465709471356340651340817787307846982853555459305892280608938) * 10 ^ 70 +
        3518414088256057631299828967530141063624482427030208000813972028674328) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 69 = 7 +
      62 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_211_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_211_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_212_prefix_zero :
    (∑ x ∈ Finset.range 48,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (212 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (212 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_212_suffix_zero :
    (∑ x ∈ Finset.range 63,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (212 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_212 :
    recurrence5B1A3.coeff 212 =
      ((((21730866 * 10 ^ 70 +
        9212884718067363178953977770008683935771164228571309176215820200983714) * 10 ^ 70 +
        7792103897002764463488975581515098349866644129708212597762750586605502) * 10 ^ 70 +
        1143151295615856166579896845372144042849678343300387133711178929717256) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 69 = 6 +
      63 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_212_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_212_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_213_prefix_zero :
    (∑ x ∈ Finset.range 49,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (213 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (213 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_213_suffix_zero :
    (∑ x ∈ Finset.range 64,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (213 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_213 :
    recurrence5B1A3.coeff 213 =
      -((((3705583 * 10 ^ 70 +
        2783985133226448623810973801778259451462411594684398541066303228628749) * 10 ^ 70 +
        8686953999975839801623027734567091262337832716612217906205399264385090) * 10 ^ 70 +
        7449276995364027555979433556241350385058342637213582152088009045646793) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 69 = 5 +
      64 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_213_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_213_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_214_prefix_zero :
    (∑ x ∈ Finset.range 50,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (214 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (214 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_214_suffix_zero :
    (∑ x ∈ Finset.range 65,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (214 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_214 :
    recurrence5B1A3.coeff 214 =
      -((((421235 * 10 ^ 70 +
        3903460176081791154604124754344037892331359721584313672093286909549665) * 10 ^ 70 +
        0632182762951011656806632710151250035285978996641248593009369120918687) * 10 ^ 70 +
        5315399510973165997742630496122375972900190811041493096151151709623909) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 69 = 4 +
      65 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_214_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_214_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_215_prefix_zero :
    (∑ x ∈ Finset.range 51,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (215 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (215 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_215_suffix_zero :
    (∑ x ∈ Finset.range 66,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (215 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_215 :
    recurrence5B1A3.coeff 215 =
      ((((804500 * 10 ^ 70 +
        9054267417714945479659398415506508145253262055986134820165404566569026) * 10 ^ 70 +
        8195540981397872084381048793846561325717787355087667272315131625340543) * 10 ^ 70 +
        2978225367282056727121212470187079684058805016582800497782460923020796) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 69 = 3 +
      66 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_215_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_215_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_216_prefix_zero :
    (∑ x ∈ Finset.range 52,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (216 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (216 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_216_suffix_zero :
    (∑ x ∈ Finset.range 67,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (216 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_216 :
    recurrence5B1A3.coeff 216 =
      -((((500391 * 10 ^ 70 +
        1417315261298425192553785875182464074384961866037431730035080119143047) * 10 ^ 70 +
        3746406204411280510118573328758001986681314964372017669803036561392785) * 10 ^ 70 +
        2452357915191370770370315949858418295134448069126264372072436918076121) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 69 = 2 +
      67 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_216_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_216_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_217_prefix_zero :
    (∑ x ∈ Finset.range 53,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (217 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (217 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_217_suffix_zero :
    (∑ x ∈ Finset.range 68,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (217 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_217 :
    recurrence5B1A3.coeff 217 =
      ((((237142 * 10 ^ 70 +
        7135719865686587007320314450714139296646413577273072971759564641604467) * 10 ^ 70 +
        4115480429313470707998534123961826066678077159472197025002255236551206) * 10 ^ 70 +
        4889454087389417314501725750835269187966613456138538016248254445075939) : ℚ) := by
  unfold recurrence5B1A3
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
    rw [show 69 = 1 +
      68 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_217_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_217_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B1A3_coeff_218_prefix_zero :
    (∑ x ∈ Finset.range 54,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (218 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (218 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_218_suffix_zero :
    (∑ x ∈ Finset.range 69,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (218 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_218 :
    recurrence5B1A3.coeff 218 =
      -((((96974 * 10 ^ 70 +
        1987984446919245652789344979551161880668959896863176242109012358079752) * 10 ^ 70 +
        7122809058969689464147973479232192172109083057242984086151120232909337) * 10 ^ 70 +
        4643990619779582481603864028768459212604674215392200434298172040613601) : ℚ) := by
  unfold recurrence5B1A3
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
  rw [recurrence5B1A3_coeff_218_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_218_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
