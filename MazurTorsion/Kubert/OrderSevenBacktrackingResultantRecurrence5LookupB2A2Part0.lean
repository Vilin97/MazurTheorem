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

theorem recurrence5B2A2_coeff_0 :
    recurrence5B2A2.coeff 0 =
      (7089163485397076864120412862377044524896337959722123147124301376024576 : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_1 :
    recurrence5B2A2.coeff 1 =
      -((3688 * 10 ^ 70 +
        4053808886215649946829585246044451727990968296257400154687098363832320) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_2 :
    recurrence5B2A2.coeff 2 =
      ((9014873 * 10 ^ 70 +
        5658912254089467323230629352753304809831189427573154290370119836837264) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_3 :
    recurrence5B2A2.coeff 3 =
      -((48851548102 * 10 ^ 70 +
        8696986141661748141389526488382373577978578692203730992938097417021072) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_4 :
    recurrence5B2A2.coeff 4 =
      ((125929843425479 * 10 ^ 70 +
        7684722749450195377191895542226298879873777943936908240029087391482984) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_5 :
    recurrence5B2A2.coeff 5 =
      -((163563701585351856 * 10 ^ 70 +
        7737616806849615346104409417407247238611011609697913515966629553078680) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_6 :
    recurrence5B2A2.coeff 6 =
      ((137205676214249565361 * 10 ^ 70 +
        0502949582509720004930747685685340920893144489868528706996795282764712) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_7 :
    recurrence5B2A2.coeff 7 =
      -((75783561990260462389403 * 10 ^ 70 +
        3350864569201376133831538684976585753757939889031311744071874842565600) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_8 :
    recurrence5B2A2.coeff 8 =
      ((27788777058250562146950157 * 10 ^ 70 +
        8199388834042739202687901716823092053454912252938695791364742064993644) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_9 :
    recurrence5B2A2.coeff 9 =
      -((5924825367302685078045825714 * 10 ^ 70 +
        8159207335846649409064767995716645426576917677546922123732663699023608) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_10 :
    recurrence5B2A2.coeff 10 =
      -((2964630018382338539172293104234 * 10 ^ 70 +
        8436345271405810538535010950018113622295379780560452013714587380059932) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_11 :
    recurrence5B2A2.coeff 11 =
      ((6389559489484450412787946864691010 * 10 ^ 70 +
        4213861953683407843835498886998688584005751837641601453170854380961572) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_12 :
    recurrence5B2A2.coeff 12 =
      -((5599733385084356374902900914226604395 * 10 ^ 70 +
        3543396957746712722915902372603022056235020869534608745885014103773264) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_13 :
    recurrence5B2A2.coeff 13 =
      ((2938157584804285512244943740681852656748 * 10 ^ 70 +
        0860892257194029780933495429433833587827300768451111245576482452574258) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_14 :
    recurrence5B2A2.coeff 14 =
      -((875009102087810682058007683113871967598049 * 10 ^ 70 +
        3728052920938979529794212793931359933010780946152725917834196651182734) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_15 :
    recurrence5B2A2.coeff 15 =
      ((26170026121007258740197053040592021282485545 * 10 ^ 70 +
        8758415089108228162869134484053411250264806573143574434105492188200704) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_16 :
    recurrence5B2A2.coeff 16 =
      ((122893444694317917648658210754876259240338460633 * 10 ^ 70 +
        8413583228870844617135315659484708153157698248283705776078289005023450) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_17 :
    recurrence5B2A2.coeff 17 =
      -((75874446955439368434834530513623719881562080979411 * 10 ^ 70 +
        1275926373670053227667214186515050855164174459848103217573579493581513) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_18 :
    recurrence5B2A2.coeff 18 =
      ((28617589130721800092357446807331030658603108348026849 * 10 ^ 70 +
        7594381739354218197630352763862209045984336128857630170252085959716403) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_19 :
    recurrence5B2A2.coeff 19 =
      -((8047287064818666517271392806924919113192731468276517464 * 10 ^ 70 +
        4278270341974050301629195077601066888324874575609460940519700938785546) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_20 :
    recurrence5B2A2.coeff 20 =
      ((1795991171120275264244315427328023438646066886829220285006 * 10 ^ 70 +
        6185059657753176707151201491772514760185151748715140644518249489221907) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_21 :
    recurrence5B2A2.coeff 21 =
      -((326371408388809844283407052183912046035955323635951435412812 * 10 ^ 70 +
        0553960186956048487705519934725514405785784249220208658837419525307722) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_22 :
    recurrence5B2A2.coeff 22 =
      ((48617358462397992202283343605124649312015411672463503935432148 * 10 ^ 70 +
        2550396270302402471194432623504081809490490030272649799438283470468428) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_23 :
    recurrence5B2A2.coeff 23 =
      -((5864024846669954842329207746322074515878585462021073632487033764 * 10 ^ 70 +
        3065966838471765809827307200075730883703288047747056320627630005072720) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_24 :
    recurrence5B2A2.coeff 24 =
      ((544242317473896401756614952626400609743026255254890696280813711958 * 10 ^ 70 +
        5757296969269083492908970601154298056871342190827759801899146201760911) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_25 :
    recurrence5B2A2.coeff 25 =
      -((31653901161175883779618176397583362887893600090822029353568804659244 * 10 ^ 70 +
        3863029381581804044880975405194739689354856522415900883045198513679369) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_26 :
    recurrence5B2A2.coeff 26 =
      -((618849439258475297674292260533193060266171219081640744917385813467999 * 10 ^ 70 +
        8351898995406076506781896086407967747039271168242114254492447168002219) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_27 :
    recurrence5B2A2.coeff 27 =
      (((48 * 10 ^ 70 +
        4070208833307884660121309848628856460880232036054739990848668142205505) * 10 ^ 70 +
        2599812052429718894889008665573132538361263079551046079142351320470066) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_28 :
    recurrence5B2A2.coeff 28 =
      -(((8217 * 10 ^ 70 +
        7552451115143396834258549869516635634975043114260353067035749297952343) * 10 ^ 70 +
        3630902206332667568822824373800733812274465554679248693777346419925502) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_29 :
    recurrence5B2A2.coeff 29 =
      (((987514 * 10 ^ 70 +
        6772841549193476410536220393353509145101253513931111490408656469259986) * 10 ^ 70 +
        7971874290252132653113735008116959270899579138043903374228530270335396) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_30 :
    recurrence5B2A2.coeff 30 =
      -(((96785587 * 10 ^ 70 +
        3317117495487817509169522761897270684969955656872490990504181356667251) * 10 ^ 70 +
        4083099077528078739115787588181496954457307231850710603920991225820789) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_31 :
    recurrence5B2A2.coeff 31 =
      (((8132134966 * 10 ^ 70 +
        9660507319298160811978156376364086933993793842972703372525698560999416) * 10 ^ 70 +
        4318224643830212057578528385814808196517214856486302794685442848008824) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_32 :
    recurrence5B2A2.coeff 32 =
      -(((600250466463 * 10 ^ 70 +
        9696902185397376236127560872199017380083290172039849605798680567186761) * 10 ^ 70 +
        6449821730085531358712521751812412284170065060433266914634286532028822) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_33 :
    recurrence5B2A2.coeff 33 =
      (((39484813768129 * 10 ^ 70 +
        0510448497405275523634935580630495774866373073935069966345449565931068) * 10 ^ 70 +
        6409597966915423366380070904779368781176478758467566070102191860701505) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_34 :
    recurrence5B2A2.coeff 34 =
      -(((2336761743209574 * 10 ^ 70 +
        6570952465076314119139190835392421033733604742142739485557529467267371) * 10 ^ 70 +
        1638793330276751753331958229324753357657489525925978209289294662631481) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_35 :
    recurrence5B2A2.coeff 35 =
      (((125263293958554365 * 10 ^ 70 +
        2557235163837467296055891908565860499812181318905865643234526232324273) * 10 ^ 70 +
        0176759057276454578065139457255528295395854108032469806292545886634439) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_36 :
    recurrence5B2A2.coeff 36 =
      -(((6113171917709919720 * 10 ^ 70 +
        4601047042137896442094805282737661170243996092527487782995184384132296) * 10 ^ 70 +
        9510440177668979129532385320464305051152087145623449287334606327211277) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_37 :
    recurrence5B2A2.coeff 37 =
      (((272681263433017153035 * 10 ^ 70 +
        7068346809386314773626742767460568773953283837181335087814954471263840) * 10 ^ 70 +
        8282971069893900996770639774327558594538837469718364906528240713367092) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_38 :
    recurrence5B2A2.coeff 38 =
      -(((11151529024263341354531 * 10 ^ 70 +
        2375587194568951215475191507312484256570581352320419573692748072146954) * 10 ^ 70 +
        3447597584757635584556378554241915063627724713975813958949707785085384) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_39 :
    recurrence5B2A2.coeff 39 =
      (((419130127802761689977536 * 10 ^ 70 +
        4244500582998092601007874186679702537194526361225267677711500320799593) * 10 ^ 70 +
        1475589480016272820006427058036876449273143075712315981024691899861075) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_40 :
    recurrence5B2A2.coeff 40 =
      -(((14503529221952845627542703 * 10 ^ 70 +
        6090669676324312606895788372345078710005589012136037346825346387000551) * 10 ^ 70 +
        9443171251191096359479530695232298911181658269033036643729490142375592) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_41 :
    recurrence5B2A2.coeff 41 =
      (((462607481272616324554931004 * 10 ^ 70 +
        8324616489907851295745900961255332668649196388510620200197322117566065) * 10 ^ 70 +
        3306474776768707133673091174612349181404284532135041654617594245565862) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_42 :
    recurrence5B2A2.coeff 42 =
      -(((13607062064637283342900933632 * 10 ^ 70 +
        4102793488542079038425961453639371176352389989025819711108058516365502) * 10 ^ 70 +
        1392946628304170569220462640271968615542128436967209931783829301197014) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_43 :
    recurrence5B2A2.coeff 43 =
      (((368930132088778983227126992098 * 10 ^ 70 +
        2828239280770354135194063507357388274486013993785022343930871378165717) * 10 ^ 70 +
        8300838596255914004099516948270334111656884510988544590562455258808122) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_44 :
    recurrence5B2A2.coeff 44 =
      -(((9205201264392465303434056312971 * 10 ^ 70 +
        3734603803218981788671203111724892722464200259553046862058139312366660) * 10 ^ 70 +
        9537907733106251891701993421072028229422867873055306238834297828120862) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_45 :
    recurrence5B2A2.coeff 45 =
      (((210616444349787164067999961536138 * 10 ^ 70 +
        5318361601574868592618517765046325361101314926870305451081876342227487) * 10 ^ 70 +
        6342135586805367192184392825123648169893864312332498048630307010989824) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_46 :
    recurrence5B2A2.coeff 46 =
      -(((4389190364128905742187533378174064 * 10 ^ 70 +
        2311049334335451702834812698330722185279592834811426350277178478295066) * 10 ^ 70 +
        4552303323518984933721304292995370148034960106555881421051363825779183) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_47 :
    recurrence5B2A2.coeff 47 =
      (((82243016273852068010720196322418306 * 10 ^ 70 +
        8750330997258574431863057512384459959680165073798252740990362882637111) * 10 ^ 70 +
        6802393630544918496107724715579451358141088527139134991731117318442487) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_48 :
    recurrence5B2A2.coeff 48 =
      -(((1349106093067365204702376357266649440 * 10 ^ 70 +
        2013376256045662837427508915507673193245970787437055819716630793831998) * 10 ^ 70 +
        4703219528777525267620328493903953051025594214328734281795258734440824) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_49 :
    recurrence5B2A2.coeff 49 =
      (((18139097193687483961860052417385802856 * 10 ^ 70 +
        3459105903248854175995716441340416034386047689514987935176742622520953) * 10 ^ 70 +
        0569187135399481544284242070726620076036204335998583863307250549301258) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_50 :
    recurrence5B2A2.coeff 50 =
      -(((156089033468443749748852965130128392065 * 10 ^ 70 +
        0422614529388558404430722243424079734380670652681861979403852995953306) * 10 ^ 70 +
        2041499236638168720935967910793788557250369014918486589208413520965508) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_51 :
    recurrence5B2A2.coeff 51 =
      -(((924229976524615676239459388616296765075 * 10 ^ 70 +
        1766220616797627610347862589936100360796511222549415014751171076299265) * 10 ^ 70 +
        6870016344590452509574242705084009038625157806242970101182259948904754) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_52 :
    recurrence5B2A2.coeff 52 =
      (((85437999703801690839331260682156184338409 * 10 ^ 70 +
        6222108937677433160258258806715011547157165821501712732742582939319191) * 10 ^ 70 +
        8169406038906989974295059960191998177986564162769702408049761991078605) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_53 :
    recurrence5B2A2.coeff 53 =
      -(((2611730360583822964781191867243626297371305 * 10 ^ 70 +
        8636150068374157110765878464653071189146540716321908312756067789986036) * 10 ^ 70 +
        4853126686405429534077725579967264988316850458822866346305385500478104) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_54 :
    recurrence5B2A2.coeff 54 =
      (((60671058496470928873159918388077236977626298 * 10 ^ 70 +
        5890563576231999187817423914333884341485498319257774480677229718033988) * 10 ^ 70 +
        6125986285315417805011301316012996660098557122178132603239753334237227) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_55 :
    recurrence5B2A2.coeff 55 =
      -(((1211686482205638331967804763915062326584453239 * 10 ^ 70 +
        1854999419147102062492110151595632637427611666348806781596055031982397) * 10 ^ 70 +
        2006519373119847472380253693744409566054933825236936657142813029119527) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_56 :
    recurrence5B2A2.coeff 56 =
      (((21738924492547708846950341920785889203764988210 * 10 ^ 70 +
        0129638518564415993712794846600286221713870366099701664899704047629210) * 10 ^ 70 +
        8898328866573435836899879267241053549553712899793886839545529188667727) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_57 :
    recurrence5B2A2.coeff 57 =
      -(((357852884647199933757827445217690890022435221907 * 10 ^ 70 +
        6982096550844533775176422242001139962890632631787710177309500441415231) * 10 ^ 70 +
        6007887098591330863378705515043274803090754093326571906852000781561327) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_58 :
    recurrence5B2A2.coeff 58 =
      (((5470403225297384015718666382662210441499378820738 * 10 ^ 70 +
        6610190646428507961389934108730267587705522776267148819817932375626046) * 10 ^ 70 +
        6064213332224204216953261970123514166621521105838278572824249902614126) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_59 :
    recurrence5B2A2.coeff 59 =
      -(((78255813796918190434793202172333640665916531935088 * 10 ^ 70 +
        4747585040149051062353341728250243046592991523734748603504437284464357) * 10 ^ 70 +
        4134281411350162299839961012038281987259718989027742445469639692073525) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_60 :
    recurrence5B2A2.coeff 60 =
      (((1053180037929077656267813509692289938959602369396713 * 10 ^ 70 +
        6221913380078782540961791939511251010290963379500957910900444839168967) * 10 ^ 70 +
        0409689959922254517752327366044625782577741837259513560267917623869016) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_61 :
    recurrence5B2A2.coeff 61 =
      -(((13386747642077181505846660399747492976455910767557295 * 10 ^ 70 +
        9452867941496936576909134926441775095608000870909157534872870965676293) * 10 ^ 70 +
        8710276165226030522870610627665810653891982536400997651540229029960913) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_62 :
    recurrence5B2A2.coeff 62 =
      (((161193062057951360599109497665856803699460958918259482 * 10 ^ 70 +
        6189552634717119052751160935272615694822074233318686944542198226437052) * 10 ^ 70 +
        5513340601583191567772406617272031100089769227282652656181179908418073) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_63 :
    recurrence5B2A2.coeff 63 =
      -(((1843195299552320616975130914776383920904339109277687720 * 10 ^ 70 +
        2471735013705905327413495839145889022587873542793947878767996622054510) * 10 ^ 70 +
        3529853545813192301640336749005284360919798408019169085069342654638618) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_64 :
    recurrence5B2A2.coeff 64 =
      (((20055122346336142727126686076690644571192584950787701376 * 10 ^ 70 +
        6591046977753552328292870164213237868437263299147817987423507471433090) * 10 ^ 70 +
        1955712651131770969430198224380112882139980803848197951509871730426819) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_65 :
    recurrence5B2A2.coeff 65 =
      -(((207995160275844324352496826627381053230843688600412919919 * 10 ^ 70 +
        5904803999474120835967911573977039419279496055850202587927110116495006) * 10 ^ 70 +
        5848229837858558279484089278851796157729515110909540166176190768129396) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_66 :
    recurrence5B2A2.coeff 66 =
      (((2059219693807744990374753194587559211290235008303004565075 * 10 ^ 70 +
        8244108478526356722436070987998327145199532596709806512940419759904269) * 10 ^ 70 +
        3873405377897041540356330344837106898384260806066131080210056849271099) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_67 :
    recurrence5B2A2.coeff 67 =
      -(((19487059868304319110718731447515108778362951239648038034415 * 10 ^ 70 +
        4216880486457597695230665916999220275341600455158524860358651589198107) * 10 ^ 70 +
        4349182436694347522018044233345860941940644579733344493024282143808057) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_68 :
    recurrence5B2A2.coeff 68 =
      (((176480888077823360649534955151811542635248098985814370395522 * 10 ^ 70 +
        4527043071879651201246696879557415796134472332787914213586087651670678) * 10 ^ 70 +
        0193742225990780190720207383693293914948357430094055230597077199865648) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_69 :
    recurrence5B2A2.coeff 69 =
      -(((1531167341479300151195926750494866906591069906865334395853447 * 10 ^ 70 +
        8163702630791391836761178826583659594882786633387525229945120530609816) * 10 ^ 70 +
        9467744310801704243317525421578877824011466179428218638876450443897126) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_70 :
    recurrence5B2A2.coeff 70 =
      (((12739370020080226133236571201990773960353869616209315501083254 * 10 ^ 70 +
        8913496227300945925959360657581498157674374938113468218268980656444644) * 10 ^ 70 +
        8529954708546516413949315631320160341769550256359564685928038652034223) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_71 :
    recurrence5B2A2.coeff 71 =
      -(((101734312540477273575115004059051426224910567933371754577130283 * 10 ^ 70 +
        1617655094355133091185448147897008662451637786160789311803317115442159) * 10 ^ 70 +
        0696097656898261623461574005715842536017570327207576494973118147115170) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_72 :
    recurrence5B2A2.coeff 72 =
      (((780453683873536383034834195666905017961730813784097338794131362 * 10 ^ 70 +
        4535087680321372937870428804790207301538532228293860003952138738801308) * 10 ^ 70 +
        2134514841828402983643287906508001090050926175033290623134702964345113) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_73 :
    recurrence5B2A2.coeff 73 =
      -(((5756106929282088594590061208225838189904170524644448809868473591 * 10 ^ 70 +
        3943576541314589658548547649833304903025211114890074242970468414385046) * 10 ^ 70 +
        4342947782729341849039751575754218064224458207676373790786209285472307) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_74 :
    recurrence5B2A2.coeff 74 =
      (((40844480349461761731221107286656639244706245846666915523387424990 * 10 ^ 70 +
        0254085371240494380839125985544307405195237939410379406649801373129291) * 10 ^ 70 +
        8403985636787296527897258080001974176846222021427761192440048688439866) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_75 :
    recurrence5B2A2.coeff 75 =
      -(((279037638305855005621516864862194538149889131266693461034964207160 * 10 ^ 70 +
        5680987415042719383708087173109046450702044180808453160771367445270472) * 10 ^ 70 +
        9032611467705658118031796543782121923942205638941925097789506473491298) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_76 :
    recurrence5B2A2.coeff 76 =
      (((1836548740013030262924610707820855616067317082673476856065890668006 * 10 ^ 70 +
        2897059814544072963178382673036631631472439066015145852817342404658840) * 10 ^ 70 +
        0838343660968601894835156970128119169161628658898590085150928884000853) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_77 :
    recurrence5B2A2.coeff 77 =
      -(((11652594856668956858649370946970614957376680580401161361924147930616 * 10 ^ 70 +
        0960541919830681654380468547225516347376233570872545292164410612702774) * 10 ^ 70 +
        5907136113005436177253524173084364690191575427915924060955771257278815) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_78 :
    recurrence5B2A2.coeff 78 =
      (((71314827927890164056732134584672701507787493131075124784219186007611 * 10 ^ 70 +
        5376714466172353595054924245391810886479417821749708568851007558962092) * 10 ^ 70 +
        5067616007145373458806835186277988884167672533103543923305540542041861) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_79 :
    recurrence5B2A2.coeff 79 =
      -(((421228616663034190732313408594852693293014642341852561478235879090382 * 10 ^ 70 +
        0064047474810429506780674133744249342815598525060152967671816511144911) * 10 ^ 70 +
        4433785409964047666473386806145453335725553127092509793371699991231481) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_80 :
    recurrence5B2A2.coeff 80 =
      (((2402530265283575078342231831584694031538281247754874263006078254644419 * 10 ^ 70 +
        3026194519043209629501189843517424214825077717188182854867150763102393) * 10 ^ 70 +
        7087298800549955425078956276000134314160809966705670684494039172843992) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_81 :
    recurrence5B2A2.coeff 81 =
      -((((1 * 10 ^ 70 +
        3238966475436839317380033402390774567512676807295694484519011032164909) * 10 ^ 70 +
        6894948572244815663513290735144940738095161882586420002990151500491958) * 10 ^ 70 +
        4613899887192544017108938059182103261478889846428700327110052297859305) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_82 :
    recurrence5B2A2.coeff 82 =
      ((((7 * 10 ^ 70 +
        0515497580950612130681100962858265201457071542341232761908426307942555) * 10 ^ 70 +
        8598794197878430584650873050110154942614987165950823229812904515068986) * 10 ^ 70 +
        6073895448105744458928553352813696809128303371951607564608958769939903) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_83 :
    recurrence5B2A2.coeff 83 =
      -((((36 * 10 ^ 70 +
        3213378299973973485143750320501061834526639899428871149719144471509159) * 10 ^ 70 +
        4045090916432881210172745198613885145368440481466949181863645993801129) * 10 ^ 70 +
        4921683288873767811601560523921417046477659672264989079962438063703817) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_84 :
    recurrence5B2A2.coeff 84 =
      ((((180 * 10 ^ 70 +
        9998988791178237078335605771777252727934523352130104610796741299451605) * 10 ^ 70 +
        1518899156089218672771781414427944636659476311193559874234413183040473) * 10 ^ 70 +
        9301403894494717673073552821638916614768753948110789090044573894078856) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_85 :
    recurrence5B2A2.coeff 85 =
      -((((873 * 10 ^ 70 +
        0075109487188009091374821635474901611777505580477935247680749316674964) * 10 ^ 70 +
        2695546479636040656355600693953783125408150436807077397105864671009126) * 10 ^ 70 +
        3507391427181059413178883654476022333317252462081080926685210882637267) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_86 :
    recurrence5B2A2.coeff 86 =
      ((((4077 * 10 ^ 70 +
        1490230447364752901323139452046624579744925636829468481532011890321060) * 10 ^ 70 +
        0594776458144579604856987934930078386646462823524106110368273082427222) * 10 ^ 70 +
        4434942677290500257551086093988219178590209403080566591976538424267577) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_87 :
    recurrence5B2A2.coeff 87 =
      -((((18444 * 10 ^ 70 +
        3023124694250755111834682906437604781614856132643663234778360410582256) * 10 ^ 70 +
        6116961631920518123935211411730517156237533575644826540682756699692772) * 10 ^ 70 +
        1721889259406872167618647499437166661598819759886151743018967839680218) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_88 :
    recurrence5B2A2.coeff 88 =
      ((((80852 * 10 ^ 70 +
        9070109249466637602694475358737552746301737000837296472352028030608329) * 10 ^ 70 +
        8359601672223710930894594381097608876008373039906943189521783729020228) * 10 ^ 70 +
        9922433770865639264920923812095945461969364723198838304214713878687165) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_89 :
    recurrence5B2A2.coeff 89 =
      -((((343566 * 10 ^ 70 +
        2488609214782672839421002806178458310520411507836622532093687637591698) * 10 ^ 70 +
        8959314871393467583974144963535222966714663149212833474115639821756072) * 10 ^ 70 +
        8441001330386344111061462025672618729904235209640091891096266847587577) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_90 :
    recurrence5B2A2.coeff 90 =
      ((((1415643 * 10 ^ 70 +
        0139247743251244640083666642542413127596873994847862119348415669689550) * 10 ^ 70 +
        0607542915152697907575911709542663067916630660749139529864721522224285) * 10 ^ 70 +
        2586515705553507261180958074663943091119336918302928558484357056109674) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_91 :
    recurrence5B2A2.coeff 91 =
      -((((5658038 * 10 ^ 70 +
        8070477342552200736316327039027470574577705610719907820419035420813822) * 10 ^ 70 +
        4267572733213529856594228789062715573847255259280674941940717360178947) * 10 ^ 70 +
        4714092209477331437529990739430040742338864802766302600242721003289538) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_92 :
    recurrence5B2A2.coeff 92 =
      ((((21942259 * 10 ^ 70 +
        2789034495867908384701560344649264545188698359194215906640089623648479) * 10 ^ 70 +
        4463685898435152466542559196043167651865812893511025772763453903771979) * 10 ^ 70 +
        6785650647713401205256658483561293616471090117696012870571767220731852) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_93 :
    recurrence5B2A2.coeff 93 =
      -((((82590181 * 10 ^ 70 +
        3400018444576396210623542737194579006242747588643744389477132590730273) * 10 ^ 70 +
        6021891301639565623648110882358469823640035852977649552773028061041512) * 10 ^ 70 +
        4079630697648976547374284755742003949494747988824185544504064076827418) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_94 :
    recurrence5B2A2.coeff 94 =
      ((((301807391 * 10 ^ 70 +
        1617049643893079763184230586582885177295664243642062621326842056326304) * 10 ^ 70 +
        5833234929649940000446711490109947147774706866709347732581206671040497) * 10 ^ 70 +
        2189436910356842218621760148779072702460973760999100741653807588146865) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_95 :
    recurrence5B2A2.coeff 95 =
      -((((1071033242 * 10 ^ 70 +
        9409243246195550304837141828660888500182183937789181522700130460292390) * 10 ^ 70 +
        2019089912401825356556482432854631403873219993109596389966151602897094) * 10 ^ 70 +
        8496065494472121045656897348475164484690360057731525755320253042226827) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_96 :
    recurrence5B2A2.coeff 96 =
      ((((3691982719 * 10 ^ 70 +
        5592972359579109429186261251075616273458022628323088421575857113672925) * 10 ^ 70 +
        9422511866984661166605747625059223795612132651850697465532170620721012) * 10 ^ 70 +
        6765838027349155092287697418105276383320887248106960495290403734901328) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_97 :
    recurrence5B2A2.coeff 97 =
      -((((12365365264 * 10 ^ 70 +
        6589058981418811238142519272126801851734032707852927985413992816434353) * 10 ^ 70 +
        7311409831898339913304290901442124611708579768991935936217066576316559) * 10 ^ 70 +
        3192554591784224356617452171751633561973655889614592436478989257370690) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_98 :
    recurrence5B2A2.coeff 98 =
      ((((40248241869 * 10 ^ 70 +
        4064168567406052149778420520865044153236552818660055241011445942575449) * 10 ^ 70 +
        8683676858580081958311163948231379131579378257874777813874413167541335) * 10 ^ 70 +
        9448848821936706412244842756976791522617850333694126736651908163177523) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_99 :
    recurrence5B2A2.coeff 99 =
      -((((127343554884 * 10 ^ 70 +
        1828911731984290207583893448897505458093567326347705603012784368934781) * 10 ^ 70 +
        3091657309771594531226087549002690295375745316257766966366854878880217) * 10 ^ 70 +
        0508067981682259589412952427675431566925910381655707932917130307750098) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_100 :
    recurrence5B2A2.coeff 100 =
      ((((391732879459 * 10 ^ 70 +
        7427643215416718845335455253018927972748807365328160432227463804230814) * 10 ^ 70 +
        1510931293277508294192418652275390277178240183000274560344024970196229) * 10 ^ 70 +
        0627846492812496946166968730111384900816930035874651587100162899066132) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_101 :
    recurrence5B2A2.coeff 101 =
      -((((1171857071637 * 10 ^ 70 +
        5017156334833059129179576472914530447287242297506905566966105070530049) * 10 ^ 70 +
        2149472328022306014094152658051250641681979304252068885228447261485548) * 10 ^ 70 +
        5130116125511181512562042252419500552501528153302756675248622851149545) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_102 :
    recurrence5B2A2.coeff 102 =
      ((((3409692383599 * 10 ^ 70 +
        7201059529740609188670848835106208024231438005993559420264958929582181) * 10 ^ 70 +
        9550608117999434805814838119344764058694389076711882409607225456585167) * 10 ^ 70 +
        4024260879911434830478778414112183500600411545644137258921188124860990) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_103 :
    recurrence5B2A2.coeff 103 =
      -((((9651437493822 * 10 ^ 70 +
        9126297673338650463137156251381133107616014937723941308473347905808865) * 10 ^ 70 +
        6438516156078266504113308244609162808544432654876655781687989148908055) * 10 ^ 70 +
        3691434181434956476814639004324490661973989120695643403153195188512343) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_104 :
    recurrence5B2A2.coeff 104 =
      ((((26581619854619 * 10 ^ 70 +
        3562753264747427363711376780229107243498576625950141042219281616196441) * 10 ^ 70 +
        9716952000591354057829693823951303295426047399025325201915526137328526) * 10 ^ 70 +
        0854825959003002961185256598344842367944297305200243831883409610196888) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_105 :
    recurrence5B2A2.coeff 105 =
      -((((71245280864986 * 10 ^ 70 +
        0965233762421488390098260226391344042653238247308123242845352559297473) * 10 ^ 70 +
        2845341617082194937183748741842860170448351609877631953412718482203522) * 10 ^ 70 +
        5689825244364636425902410125469741780062932140963845705253953113998588) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_106 :
    recurrence5B2A2.coeff 106 =
      ((((185859542894105 * 10 ^ 70 +
        5589178584773692291917720061237733906663748542755458695513913933359167) * 10 ^ 70 +
        7599297501402621419348192854265969038093796235389402886505250476686227) * 10 ^ 70 +
        8383434759754990981951026149357300824273546789526105025259344923768374) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_107 :
    recurrence5B2A2.coeff 107 =
      -((((471990226786249 * 10 ^ 70 +
        3007371945341063809079934261700844087585109273966680460198554035105702) * 10 ^ 70 +
        2634364897944920191243725735861275663867484651312304125388823956519389) * 10 ^ 70 +
        2138854441299160558658323370136476785826980077175707396996188214708254) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_108 :
    recurrence5B2A2.coeff 108 =
      ((((1166976965403216 * 10 ^ 70 +
        2522806872149139369666654520946119250247077636641241923059711949957906) * 10 ^ 70 +
        5355332137343641333732811487231003584026822417706426848292058528023277) * 10 ^ 70 +
        4174319121695281041409975196921760804363286231882887932045939420660854) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_109 :
    recurrence5B2A2.coeff 109 =
      -((((2809512729888342 * 10 ^ 70 +
        6559076197089776256313804342366989945590195839888599370786278632042041) * 10 ^ 70 +
        1608782193116507740905565032505233345341329567699740617381099705716417) * 10 ^ 70 +
        3606470032033307589418579193024686821479589788720978254806201691507355) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_110 :
    recurrence5B2A2.coeff 110 =
      ((((6587097341927546 * 10 ^ 70 +
        5674141154579564096772182838604789145903751209113268555553430301581893) * 10 ^ 70 +
        6950446148338299072345464290066344461499842989103446192929904437165877) * 10 ^ 70 +
        3954448132701024412102917838547525058550550087217474275203707048391836) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_111 :
    recurrence5B2A2.coeff 111 =
      -((((15041913258241375 * 10 ^ 70 +
        0935595078208248310919028456264727035042997734496736134927269656095672) * 10 ^ 70 +
        3567439841948837452341339576918930975297823782554035497637983745086953) * 10 ^ 70 +
        9431572252054411815620851861789276713161329731451155018265350045215156) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_112 :
    recurrence5B2A2.coeff 112 =
      ((((33458482888917482 * 10 ^ 70 +
        1797025604943672453512607791912991937538327711635072234403551451981249) * 10 ^ 70 +
        1330999080980560251822190678703424587346401568568242377908299228693292) * 10 ^ 70 +
        7854003413456470292406350338206452736399793472314162215152431450572590) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_113 :
    recurrence5B2A2.coeff 113 =
      -((((72501754193905053 * 10 ^ 70 +
        3961439426370585284222838506629345377506357075248262680955565789901174) * 10 ^ 70 +
        5420883082821868261973666304217662864105105325143575470377324936900578) * 10 ^ 70 +
        8659240082683033608629499237664630102722521697598463327086064097536035) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_114 :
    recurrence5B2A2.coeff 114 =
      ((((153063457052475849 * 10 ^ 70 +
        3101291127840197505442809844187094415909137536870536259296898684863859) * 10 ^ 70 +
        9342270312055538950649213721963595954765741725089439959283653737295466) * 10 ^ 70 +
        5641955321660104460879159022185036896823676678915219197150595941418034) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_115 :
    recurrence5B2A2.coeff 115 =
      -((((314857145073782954 * 10 ^ 70 +
        7066398256554755782063954161963935464464882766761895894956274160895761) * 10 ^ 70 +
        2334063482456289022374881945621549551226581249477722751428122671770706) * 10 ^ 70 +
        6696366752564614826971600966329687997388517978610219479623085832399897) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_116 :
    recurrence5B2A2.coeff 116 =
      ((((631116517679844310 * 10 ^ 70 +
        3799601380523872578828568721774644308242591167734197662863419120410426) * 10 ^ 70 +
        6874964162490484403813092825067753168726611526903460692718219364547596) * 10 ^ 70 +
        6606384815467383373676288402893783357622842588465626560168082280094990) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_117 :
    recurrence5B2A2.coeff 117 =
      -((((1232795359133047006 * 10 ^ 70 +
        4934637421688905095938538283272129927890568847084082706282392708067026) * 10 ^ 70 +
        0367663285972977659455047933051725403947010316515948732413340397863288) * 10 ^ 70 +
        7171590685078026473583179120655696210354865539048997382127078691909500) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_118 :
    recurrence5B2A2.coeff 118 =
      ((((2346852834513585399 * 10 ^ 70 +
        0443592225324596048377986728147827301323305055314563124134550093771244) * 10 ^ 70 +
        6802764861779620535412364812620708197702082593550665565466174777590800) * 10 ^ 70 +
        4865460864198755603394056119415933724793340908378586337375043074125051) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_119 :
    recurrence5B2A2.coeff 119 =
      -((((4354301348611816517 * 10 ^ 70 +
        0743721644656848628527439798054715622777739332606226501949186320130325) * 10 ^ 70 +
        2997426406732917864677808318802926220769404834653032786954711658440756) * 10 ^ 70 +
        4155350651062934163665787281202056807096986129286011688613697989167096) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_120 :
    recurrence5B2A2.coeff 120 =
      ((((7874254082736315791 * 10 ^ 70 +
        8724309187304070685629633724103730515706102941940702602697545297145997) * 10 ^ 70 +
        6985143956987251455855353910188345596987871039687511569164706499866987) * 10 ^ 70 +
        5085680985955506231328364965077094457289865307302353892490553120743645) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_121 :
    recurrence5B2A2.coeff 121 =
      -((((13879546724918867837 * 10 ^ 70 +
        1307780577373021488340366573673909476661854124180334603688837200208117) * 10 ^ 70 +
        9254247786536097822442678275723613462880730968096333228708176495260961) * 10 ^ 70 +
        5898446268879354592019953660146188084136217410405865233277093576768550) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_122 :
    recurrence5B2A2.coeff 122 =
      ((((23846710492231078035 * 10 ^ 70 +
        8680702880119597413429998977395929219720646450100809824737220948818207) * 10 ^ 70 +
        1496989362147528222042886996449620513188782049513977558194433045757775) * 10 ^ 70 +
        6770717021000882901727519319871043901002927811801171527758738351015903) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_123 :
    recurrence5B2A2.coeff 123 =
      -((((39937142218529537232 * 10 ^ 70 +
        8029606115882815354171216154475863133000346534511440936428426452907512) * 10 ^ 70 +
        0060950784428402038607351933464335712972856246382430050653413319057789) * 10 ^ 70 +
        7502304422558755449021384757818235776603744648518539067682340657635099) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_124 :
    recurrence5B2A2.coeff 124 =
      ((((65196457671023253601 * 10 ^ 70 +
        2960369348736610281167191037648624619687271984231798885109130127535920) * 10 ^ 70 +
        1403533529499854193930111391430636100186939848637624880990881598505701) * 10 ^ 70 +
        6795334197051321358141286364066447107872863758987788107859425473075810) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_125 :
    recurrence5B2A2.coeff 125 =
      -((((103745091504473692977 * 10 ^ 70 +
        8427428257332825090160959698858192905310509461395364128524924043666574) * 10 ^ 70 +
        6120487063896819736215611785316265441481022403962734341648627438362216) * 10 ^ 70 +
        1826148828696598082098257996058751606723017514380362348229464943903762) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_126 :
    recurrence5B2A2.coeff 126 =
      ((((160916305731104881067 * 10 ^ 70 +
        3941571994764731931092290941198690072548155155068608480617111692178139) * 10 ^ 70 +
        8504704151718933069754527145558600476407681968844609631614524855515743) * 10 ^ 70 +
        6346791490576179921870408769745061320901075242363632847473697781420672) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_127 :
    recurrence5B2A2.coeff 127 =
      -((((243280705416301688836 * 10 ^ 70 +
        2956731311085587942654701452085552037750728191217190836415259130267264) * 10 ^ 70 +
        1961437708958686997353931345140769929002429302004095921028695692890278) * 10 ^ 70 +
        5214245182063899430984943677443876165573364311571006185279716207941092) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_128 :
    recurrence5B2A2.coeff 128 =
      ((((358483909259281127791 * 10 ^ 70 +
        1670329952606385065954060137845599815571832582300342088123273481858811) * 10 ^ 70 +
        0223714776113934988215713850605445650994166456914936545900840131738302) * 10 ^ 70 +
        2053862761609767497218032893686761597850835833952170185302866964121434) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_129 :
    recurrence5B2A2.coeff 129 =
      -((((514822558452829591989 * 10 ^ 70 +
        5136152456492058673731652066373069650778009286171765897797647680153176) * 10 ^ 70 +
        5524161689863043431596479809419881814945369802122824291688933686568338) * 10 ^ 70 +
        6290436180166021124177592586548007277299278075850375529959535556531611) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_130 :
    recurrence5B2A2.coeff 130 =
      ((((720500174901734411824 * 10 ^ 70 +
        7529303177111636695274538363252610848789844553483247761969721745439264) * 10 ^ 70 +
        0569166170842969121304773736864642185664346170801628134013689944025853) * 10 ^ 70 +
        0175063216242494786592469694058508526784497300534286224564625288193618) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_131 :
    recurrence5B2A2.coeff 131 =
      -((((982543711071546994654 * 10 ^ 70 +
        0243903643651754380831768451782459504801356581023545019346020233946609) * 10 ^ 70 +
        9824641859220538678366534142354837831302421411750245632236890015275424) * 10 ^ 70 +
        8781222757719135348463358446243897291740678978442666762119793629406924) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_132 :
    recurrence5B2A2.coeff 132 =
      ((((1305425002461245097503 * 10 ^ 70 +
        0940368780184148256881846932703007169066387042497817063736091015245697) * 10 ^ 70 +
        3597939557977971735043733161914326061085451388539725676753893214659836) * 10 ^ 70 +
        7146473389046387902195582126812010665353819726085561034947536780355338) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_133 :
    recurrence5B2A2.coeff 133 =
      -((((1689513140213237597639 * 10 ^ 70 +
        8995772997587475348386949790585779095606221356938389264904145452746506) * 10 ^ 70 +
        7320175465355546570268091581600734023312343175725409705451647730654358) * 10 ^ 70 +
        2576868155425519012218144754422346550735697346862020122436595562939623) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_134 :
    recurrence5B2A2.coeff 134 =
      ((((2129570456951367621625 * 10 ^ 70 +
        8339765572843482149378015380767378165961986801899364483626535823825178) * 10 ^ 70 +
        1181595059949254488819631454024898957271036860849897426210673658340601) * 10 ^ 70 +
        5007004938917965061456093572886116043777791360961725956289001950893554) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_135 :
    recurrence5B2A2.coeff 135 =
      -((((2613575637465911262443 * 10 ^ 70 +
        9987235990311521823434820599016893567973035490535450763002691339011118) * 10 ^ 70 +
        0760105809075662856787992673230979404186439551932255500311688414643897) * 10 ^ 70 +
        9451052483340630949266151718528021991283627818290917651727514040245988) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_136 :
    recurrence5B2A2.coeff 136 =
      ((((3122188141341415356455 * 10 ^ 70 +
        0225376624433528276201349305580227598942617362315185858094170664338119) * 10 ^ 70 +
        9563191355570410435992079805906179254819097842774396879264371604382535) * 10 ^ 70 +
        8724131025308576746125403916741693802805104137431099675702198636977350) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_137 :
    recurrence5B2A2.coeff 137 =
      -((((3629137010654288233352 * 10 ^ 70 +
        7965745447645153020618462130347309766455744447614204233755726720913293) * 10 ^ 70 +
        2673802420271539130779978581916387629698629425605803731818393366460222) * 10 ^ 70 +
        3904827141842410934222426439563016041033085199151665968933622025058092) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_138 :
    recurrence5B2A2.coeff 138 =
      ((((4102712765597303013524 * 10 ^ 70 +
        8578938961333459092439711168281385371489393007169210560610884608448265) * 10 ^ 70 +
        8191428646438514052367117748650813117609692857271564288485720798758326) * 10 ^ 70 +
        7773093825025352543073958320837749429172260118315344200691013031843919) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_139 :
    recurrence5B2A2.coeff 139 =
      -((((4508368833495477453696 * 10 ^ 70 +
        3244790191598862140723977715173454414402195970952807990976275226542667) * 10 ^ 70 +
        7745423424651765934572035686025151441151660337010117922662336101972590) * 10 ^ 70 +
        1939363932485637696661816517921522285139992378163303545762254984244333) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_140 :
    recurrence5B2A2.coeff 140 =
      ((((4812224174622583775657 * 10 ^ 70 +
        2602020332929908583128882787335104474512084897127921652811274275959988) * 10 ^ 70 +
        0941004167079405534686744375438898245904531648545548530447380924739575) * 10 ^ 70 +
        9628271900115270146166845053978339113147132994716818214758906472327066) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_141 :
    recurrence5B2A2.coeff 141 =
      -((((4985044389577432531783 * 10 ^ 70 +
        5849562905912627210940136369390273531592897463785407327237620033020175) * 10 ^ 70 +
        5461708454516810344416586210007509275758628215314148898124072632371065) * 10 ^ 70 +
        2467867584942227685750005968740300461954045978797033421401526815475658) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_142 :
    recurrence5B2A2.coeff 142 =
      ((((5006116515161160359226 * 10 ^ 70 +
        4237379106322744719209495038372752141043944916715057794401544376132375) * 10 ^ 70 +
        0783570038138296175792009977320603347042833319038392952245624752233132) * 10 ^ 70 +
        7167330790069300700965316184259874383882776744588930354291732736767123) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_143 :
    recurrence5B2A2.coeff 143 =
      -((((4866370566923484408412 * 10 ^ 70 +
        5378971649867961887012145832197672809128699536975320094346237980881252) * 10 ^ 70 +
        9648778653667302225295736967849394281416053046921908726075221488786238) * 10 ^ 70 +
        8609025851028875058108521799572937657580318545219268838989857088934584) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_144 :
    recurrence5B2A2.coeff 144 =
      ((((4570167668511858190548 * 10 ^ 70 +
        9007399552238765157320553816147513407213027080996649816924081844710430) * 10 ^ 70 +
        1925261356547938032352452996329113103131152502494320427597252556832086) * 10 ^ 70 +
        7977846241185080445532290834436774665631088228806171085826285704452197) : ℚ) := by
  unfold recurrence5B2A2
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

theorem recurrence5B2A2_coeff_145 :
    recurrence5B2A2.coeff 145 =
      -((((4135369794274590861985 * 10 ^ 70 +
        2467138868887803631348712470098293737623777195090608642898561892868136) * 10 ^ 70 +
        4850979750765755308337488652108935839156169033363781209029498114777214) * 10 ^ 70 +
        9727936021319985226406195674396903534754188028002497362589608966610350) : ℚ) := by
  unfold recurrence5B2A2
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

private theorem recurrence5B2A2_coeff_146_suffix_zero :
    (∑ x ∈ Finset.range 1,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (146 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_146 :
    recurrence5B2A2.coeff 146 =
      ((((3591596324312756766014 * 10 ^ 70 +
        4040376560735570720867773571368750322333262527716744379067261694653482) * 10 ^ 70 +
        3258040744267560152720467915320841478729311631948401928549929998648730) * 10 ^ 70 +
        8352861406807196028159852346759307484479628827354033968954645461815421) : ℚ) := by
  unfold recurrence5B2A2
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
  rw [recurrence5B2A2_coeff_146_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_147_suffix_zero :
    (∑ x ∈ Finset.range 2,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (147 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_147 :
    recurrence5B2A2.coeff 147 =
      -((((2976897632809606240132 * 10 ^ 70 +
        5347532689148525443152600992484780605861781908802198523533177498895330) * 10 ^ 70 +
        1854806747242625596353092525376519385016898242320355434935817299793055) * 10 ^ 70 +
        2542939823145142758112408540689145851845244181974669817167478305076900) : ℚ) := by
  unfold recurrence5B2A2
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
  rw [recurrence5B2A2_coeff_147_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_148_suffix_zero :
    (∑ x ∈ Finset.range 3,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (148 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_148 :
    recurrence5B2A2.coeff 148 =
      ((((2333363575436472881344 * 10 ^ 70 +
        7248886750756025674974447482257823287187886519592626998161473476458333) * 10 ^ 70 +
        8763687822650354514655299691958916373198050420862542375465970343789243) * 10 ^ 70 +
        8929806468044289604112965516601955029037652314534485245464544817083190) : ℚ) := by
  unfold recurrence5B2A2
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
  rw [recurrence5B2A2_coeff_148_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_149_suffix_zero :
    (∑ x ∈ Finset.range 4,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (149 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_149 :
    recurrence5B2A2.coeff 149 =
      -((((1702369735843100328819 * 10 ^ 70 +
        8938399208837083044237416419449143486116281222198462622070606108627544) * 10 ^ 70 +
        1442458972028945680735561943900420087874276231999214524437817802731617) * 10 ^ 70 +
        7623452825201469436867030027871288458526781838050905736854589952261586) : ℚ) := by
  unfold recurrence5B2A2
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
  rw [recurrence5B2A2_coeff_149_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_150_suffix_zero :
    (∑ x ∈ Finset.range 5,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (150 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_150 :
    recurrence5B2A2.coeff 150 =
      ((((1120205978617354865055 * 10 ^ 70 +
        7205551863525398313669657954453881105198622338771895535223713110145424) * 10 ^ 70 +
        0587859612215546572645893451998179657689328183241176079012748556798330) * 10 ^ 70 +
        5554351705810825839628577248197415802613480129947189184388130024201587) : ℚ) := by
  unfold recurrence5B2A2
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
  rw [recurrence5B2A2_coeff_150_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_151_suffix_zero :
    (∑ x ∈ Finset.range 6,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (151 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_151 :
    recurrence5B2A2.coeff 151 =
      -((((614724961590036773893 * 10 ^ 70 +
        4858907215171443462678117622922919022309404884990172923082465225254890) * 10 ^ 70 +
        4286434456042557528062168015841477425832548937740154294848620016342922) * 10 ^ 70 +
        3319671051182130678419953747062930765108212401691598853953263257307855) : ℚ) := by
  unfold recurrence5B2A2
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
  rw [recurrence5B2A2_coeff_151_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_152_suffix_zero :
    (∑ x ∈ Finset.range 7,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (152 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_152 :
    recurrence5B2A2.coeff 152 =
      ((((203423427948641339611 * 10 ^ 70 +
        4846699892790703296072636103106646747034786800654955959490186947405595) * 10 ^ 70 +
        7772548622651077626256065019943158445403710560016769344587617101958355) * 10 ^ 70 +
        4793445654900009976969895352316762271019319472437625206238401530792477) : ℚ) := by
  unfold recurrence5B2A2
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
  rw [recurrence5B2A2_coeff_152_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_153_suffix_zero :
    (∑ x ∈ Finset.range 8,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (153 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_153 :
    recurrence5B2A2.coeff 153 =
      ((((106916740874087138284 * 10 ^ 70 +
        8728449468987132230796677316150168044348594645098691347887280252765810) * 10 ^ 70 +
        2695212899421183243835266802766367996830942485552814991697818755744569) * 10 ^ 70 +
        2389280874682832557526639142355400706118508727620632627648330949579272) : ℚ) := by
  unfold recurrence5B2A2
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
  rw [recurrence5B2A2_coeff_153_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_154_suffix_zero :
    (∑ x ∈ Finset.range 9,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (154 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_154 :
    recurrence5B2A2.coeff 154 =
      -((((319180814988951032940 * 10 ^ 70 +
        7139483950883486093946697273201226582385715550918375721562125701562833) * 10 ^ 70 +
        9432058912205207155929798378997018509600007527872567655980731218763927) * 10 ^ 70 +
        5915493606111716376112423116462073543094678443311671346551531025279636) : ℚ) := by
  unfold recurrence5B2A2
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
  rw [recurrence5B2A2_coeff_154_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_155_suffix_zero :
    (∑ x ∈ Finset.range 10,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (155 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_155 :
    recurrence5B2A2.coeff 155 =
      ((((443835607760286379353 * 10 ^ 70 +
        3255577612137270691723482445577916124784484461555541802416719309299779) * 10 ^ 70 +
        5475199822615975702849007922029897008422651819494935504183470087324636) * 10 ^ 70 +
        5355870920887538753968076582009803705470333757148607272218192964829888) : ℚ) := by
  unfold recurrence5B2A2
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
  rw [recurrence5B2A2_coeff_155_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_156_suffix_zero :
    (∑ x ∈ Finset.range 11,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (156 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_156 :
    recurrence5B2A2.coeff 156 =
      -((((496289325986925371153 * 10 ^ 70 +
        2406887386945921969699454218077121942575912541178688476807691511206535) * 10 ^ 70 +
        7368781512162656944459258347636554485887900243110472360928946981156170) * 10 ^ 70 +
        0841391814757611945258342772540487825563705749013703471843652980907548) : ℚ) := by
  unfold recurrence5B2A2
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
  rw [recurrence5B2A2_coeff_156_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_157_suffix_zero :
    (∑ x ∈ Finset.range 12,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (157 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_157 :
    recurrence5B2A2.coeff 157 =
      ((((494185506442994629755 * 10 ^ 70 +
        8659566131484884911302803552111907765361502167995776367199147985905253) * 10 ^ 70 +
        7800422086251875477695330030300822776260447121384097484238545462522409) * 10 ^ 70 +
        5012279877021849623297375508992867034890796247984855815479569113338257) : ℚ) := by
  unfold recurrence5B2A2
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
  rw [recurrence5B2A2_coeff_157_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_158_suffix_zero :
    (∑ x ∈ Finset.range 13,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (158 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_158 :
    recurrence5B2A2.coeff 158 =
      -((((455033515804669783579 * 10 ^ 70 +
        7183556757501894620164372686845690787668597051315902796917167813264350) * 10 ^ 70 +
        6194236197160930653406936581439914222073846553670683158862041731261618) * 10 ^ 70 +
        4371085466358887112868652212336171878188163639683461422689533997288283) : ℚ) := by
  unfold recurrence5B2A2
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
  rw [recurrence5B2A2_coeff_158_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_159_suffix_zero :
    (∑ x ∈ Finset.range 14,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (159 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_159 :
    recurrence5B2A2.coeff 159 =
      ((((394435761426198247513 * 10 ^ 70 +
        7870557805241407580478963796466495257182401862768984275041302695594399) * 10 ^ 70 +
        6592724683453551330275685353907779681011818300290849114000050095944586) * 10 ^ 70 +
        2930806125968883810158563437817524328806360067554706245661700817326041) : ℚ) := by
  unfold recurrence5B2A2
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
  rw [recurrence5B2A2_coeff_159_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_160_suffix_zero :
    (∑ x ∈ Finset.range 15,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (160 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_160 :
    recurrence5B2A2.coeff 160 =
      -((((325013976676649978936 * 10 ^ 70 +
        9328552902035089899267093390491098446681601410609607434300391261098746) * 10 ^ 70 +
        2307550064557033089812008066220120817099037026644937542407500855639140) * 10 ^ 70 +
        6976174168685999479369516052964533868559637725336293437822781240027425) : ℚ) := by
  unfold recurrence5B2A2
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
  rw [recurrence5B2A2_coeff_160_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_161_suffix_zero :
    (∑ x ∈ Finset.range 16,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (161 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_161 :
    recurrence5B2A2.coeff 161 =
      ((((255998934252720810493 * 10 ^ 70 +
        7340291524357882808987860764045198226683568439434499741520271817178962) * 10 ^ 70 +
        7057112952731256780148089129738635099713747339216235235883221734765937) * 10 ^ 70 +
        5147635101209892545473229698237061476629097765734259344716211314685252) : ℚ) := by
  unfold recurrence5B2A2
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
  rw [recurrence5B2A2_coeff_161_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_162_suffix_zero :
    (∑ x ∈ Finset.range 17,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (162 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_162 :
    recurrence5B2A2.coeff 162 =
      -((((193352235388629309161 * 10 ^ 70 +
        9863878040867134030166712873195903058757695525314818888786946457645627) * 10 ^ 70 +
        7453621496806989815991039965796304332312226076692307810224428976563479) * 10 ^ 70 +
        7942231519686947395305952159630521359278411080757240618565349464856376) : ℚ) := by
  unfold recurrence5B2A2
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
  rw [recurrence5B2A2_coeff_162_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_163_suffix_zero :
    (∑ x ∈ Finset.range 18,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (163 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_163 :
    recurrence5B2A2.coeff 163 =
      ((((140243002570872955636 * 10 ^ 70 +
        8304602565835728855462799638213522475849905871061343473861386258185817) * 10 ^ 70 +
        3008224687487079422258462099151097249861850431242835088597230298568131) * 10 ^ 70 +
        3713347654800730904602011045515816465352918131891231856371957529735445) : ℚ) := by
  unfold recurrence5B2A2
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
  rw [recurrence5B2A2_coeff_163_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_164_suffix_zero :
    (∑ x ∈ Finset.range 19,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (164 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_164 :
    recurrence5B2A2.coeff 164 =
      -((((97701128723464085648 * 10 ^ 70 +
        0378976790890794062598247967965980020306854851197334689409645972136450) * 10 ^ 70 +
        1351073579216086177631442296782996148065020550928162750085696715978491) * 10 ^ 70 +
        9634599125043962197488657466693469567340876456076664247274194819891512) : ℚ) := by
  unfold recurrence5B2A2
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
  rw [recurrence5B2A2_coeff_164_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_165_suffix_zero :
    (∑ x ∈ Finset.range 20,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (165 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_165 :
    recurrence5B2A2.coeff 165 =
      ((((65298957117513882171 * 10 ^ 70 +
        1583549850105939130717010595819981366060840039049660101848628364796179) * 10 ^ 70 +
        8033221725155455134153462112957927867308344139920773512821492195896611) * 10 ^ 70 +
        3262273983908145310562860097389935565464050542928530448788851198717818) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 166 = 0 +
    166 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
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
    rw [show 38 = 18 +
      20 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_165_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_166_suffix_zero :
    (∑ x ∈ Finset.range 21,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (166 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_166 :
    recurrence5B2A2.coeff 166 =
      -((((41759073492091197153 * 10 ^ 70 +
        4930691772877531746072851538083892500208912217628862364524674269330674) * 10 ^ 70 +
        7309977471261715650641885447005235782800905888929883025706166854480750) * 10 ^ 70 +
        0212594069095616216415646459421932622317460252758515417347715170259181) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 167 = 0 +
    167 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 167 = 32 +
      135 by norm_num, Finset.sum_range_add]
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
    rw [show 39 = 18 +
      21 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_166_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_167_suffix_zero :
    (∑ x ∈ Finset.range 22,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (167 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_167 :
    recurrence5B2A2.coeff 167 =
      ((((25433351661792369707 * 10 ^ 70 +
        5777028589528130812801613232066713084550309866338639937593164424541986) * 10 ^ 70 +
        8917737711551513081427901140695271635397230342010209438268017673134682) * 10 ^ 70 +
        2515872520200553145605767997936556983184542603587514496348591513994883) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 168 = 0 +
    168 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 168 = 32 +
      136 by norm_num, Finset.sum_range_add]
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
    rw [show 40 = 18 +
      22 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_167_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_168_suffix_zero :
    (∑ x ∈ Finset.range 23,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (168 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_168 :
    recurrence5B2A2.coeff 168 =
      -((((14638000150510368401 * 10 ^ 70 +
        7192277988057286262615001520229604859951807502115176746385206043570200) * 10 ^ 70 +
        6486045493198759788211934303906502288326322736678718827808741644917170) * 10 ^ 70 +
        2621281500536424054105288656497891948730311858367665883566348292808208) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 169 = 0 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
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
    rw [show 41 = 18 +
      23 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_168_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_169_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (169 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (169 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_169_suffix_zero :
    (∑ x ∈ Finset.range 24,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (169 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_169 :
    recurrence5B2A2.coeff 169 =
      ((((7856633288990164886 * 10 ^ 70 +
        4590561873265525211476185649576363143248679386149831775666809819930629) * 10 ^ 70 +
        0763559454220303507896326754626391567948636674835117167217838791498744) * 10 ^ 70 +
        7608743358247912537104522957355971156371853960303593199886001060750692) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 170 = 1 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
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
    rw [show 41 = 17 +
      24 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_169_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_169_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_170_prefix_zero :
    (∑ x ∈ Finset.range 2,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (170 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (170 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_170_suffix_zero :
    (∑ x ∈ Finset.range 25,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (170 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_170 :
    recurrence5B2A2.coeff 170 =
      -((((3838050374219387879 * 10 ^ 70 +
        2401656408374867132737323933073069950872614207606617463496985745433836) * 10 ^ 70 +
        4287356229324788115175092944458094867467840103640338929280982246324863) * 10 ^ 70 +
        3784778621921446366986195134199495701884694776098708522615808499901349) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 171 = 2 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
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
    rw [show 41 = 16 +
      25 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_170_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_170_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_171_prefix_zero :
    (∑ x ∈ Finset.range 3,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (171 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (171 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_171_suffix_zero :
    (∑ x ∈ Finset.range 26,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (171 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_171 :
    recurrence5B2A2.coeff 171 =
      ((((1619816665640600361 * 10 ^ 70 +
        1827229941673496458934083502184303169494550601086295508993852275587362) * 10 ^ 70 +
        8395307324962961740240842357891305615755055710596295806661819225263242) * 10 ^ 70 +
        4810480928164136237101522532859404224289509449513249080237824950928964) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 172 = 3 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
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
    rw [show 41 = 15 +
      26 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_171_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_171_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_172_prefix_zero :
    (∑ x ∈ Finset.range 4,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (172 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (172 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_172_suffix_zero :
    (∑ x ∈ Finset.range 27,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (172 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_172 :
    recurrence5B2A2.coeff 172 =
      -((((506339502030775564 * 10 ^ 70 +
        7363558205397575483086702183545179491052459384270340942059918908993505) * 10 ^ 70 +
        6754479502387743453518231418222582016595727771204174985936581623396956) * 10 ^ 70 +
        5685836653754310117384874503541629434693983164880503485248622025590664) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 173 = 4 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
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
    rw [show 41 = 14 +
      27 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_172_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_172_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_173_prefix_zero :
    (∑ x ∈ Finset.range 5,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (173 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (173 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_173_suffix_zero :
    (∑ x ∈ Finset.range 28,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (173 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_173 :
    recurrence5B2A2.coeff 173 =
      ((((24242150011063393 * 10 ^ 70 +
        7860565079570908682825845762313882657896513363472279805410454934466452) * 10 ^ 70 +
        9645800449236367323750932819581454976129676719933001081988789736778128) * 10 ^ 70 +
        6171228773687133093578854490018269804604432544900802861551550497463825) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 174 = 5 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
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
    rw [show 41 = 13 +
      28 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_173_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_173_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_174_prefix_zero :
    (∑ x ∈ Finset.range 6,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (174 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (174 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_174_suffix_zero :
    (∑ x ∈ Finset.range 29,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (174 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_174 :
    recurrence5B2A2.coeff 174 =
      ((((129000696157789916 * 10 ^ 70 +
        7251999923833599063791176977424745853727689325415795501088196516727641) * 10 ^ 70 +
        4143534164023998778027883556529039410112798695774302207738400177253703) * 10 ^ 70 +
        0006921835405394052488248278589456592413035766064507300758092944948121) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 175 = 6 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
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
    rw [show 41 = 12 +
      29 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_174_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_174_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_175_prefix_zero :
    (∑ x ∈ Finset.range 7,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (175 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (175 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_175_suffix_zero :
    (∑ x ∈ Finset.range 30,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (175 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_175 :
    recurrence5B2A2.coeff 175 =
      -((((133411832606396734 * 10 ^ 70 +
        5818974834347964322921720454466062756569274436462876539741508296216569) * 10 ^ 70 +
        4062942704520857218145037501223041057859715524979363580349201712133697) * 10 ^ 70 +
        1443858504220927873035847974715394466492981496083833771972601788416263) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 176 = 7 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
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
    rw [show 41 = 11 +
      30 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_175_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_175_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_176_prefix_zero :
    (∑ x ∈ Finset.range 8,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (176 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (176 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_176_suffix_zero :
    (∑ x ∈ Finset.range 31,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (176 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_176 :
    recurrence5B2A2.coeff 176 =
      ((((86939724070130767 * 10 ^ 70 +
        9537874001956178670580579011041262343911851607991560454335161010609220) * 10 ^ 70 +
        4356731416996879568624959260168763732173251299939927319446251446168394) * 10 ^ 70 +
        1356513814921215830537530767295183565614782821126590931476778811677996) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 177 = 8 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
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
    rw [show 41 = 10 +
      31 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_176_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_176_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_177_prefix_zero :
    (∑ x ∈ Finset.range 9,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (177 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (177 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_177_suffix_zero :
    (∑ x ∈ Finset.range 32,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (177 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_177 :
    recurrence5B2A2.coeff 177 =
      -((((36404753850754231 * 10 ^ 70 +
        6296176473907956995902632119608420379081691932587561730124747466063706) * 10 ^ 70 +
        2155083661198782808973167650839545630161988788714471148953832578737473) * 10 ^ 70 +
        0478487217186732772737766264642691349465064293599603489418715284410236) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 178 = 9 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
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
    rw [show 41 = 9 +
      32 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_177_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_177_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_178_prefix_zero :
    (∑ x ∈ Finset.range 10,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (178 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (178 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_178_suffix_zero :
    (∑ x ∈ Finset.range 33,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (178 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_178 :
    recurrence5B2A2.coeff 178 =
      -((((573739488851276 * 10 ^ 70 +
        1955369492499241870375539217516130906317264485705062093808365576506654) * 10 ^ 70 +
        3537294869581412385041387938311484210268918401558858278046047580375318) * 10 ^ 70 +
        0047402044938319913597300446774184341559405716821562636669808279255253) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 179 = 10 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
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
    rw [show 41 = 8 +
      33 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_178_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_178_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_179_prefix_zero :
    (∑ x ∈ Finset.range 11,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (179 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (179 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_179_suffix_zero :
    (∑ x ∈ Finset.range 34,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (179 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_179 :
    recurrence5B2A2.coeff 179 =
      ((((21189074156527968 * 10 ^ 70 +
        3027785459758880702416015308714428436310732458959970182637023268087668) * 10 ^ 70 +
        7733294849704675367879354084862914211731010294133249487511709142383139) * 10 ^ 70 +
        6657138866102087300905512632112123617260693830064383689720985673115116) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 180 = 11 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
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
    rw [show 41 = 7 +
      34 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_179_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_179_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_180_prefix_zero :
    (∑ x ∈ Finset.range 12,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (180 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (180 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_180_suffix_zero :
    (∑ x ∈ Finset.range 35,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (180 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_180 :
    recurrence5B2A2.coeff 180 =
      -((((28783548678042409 * 10 ^ 70 +
        8645126903986901549324715976100422732825811074889976388430520429500832) * 10 ^ 70 +
        1239177078391137852321040423792885892365454947625215713685132023522424) * 10 ^ 70 +
        8710704398736568214187356964154483320738033737790459779533335087980200) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 181 = 12 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
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
    rw [show 41 = 6 +
      35 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_180_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_180_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_181_prefix_zero :
    (∑ x ∈ Finset.range 13,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (181 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (181 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_181_suffix_zero :
    (∑ x ∈ Finset.range 36,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (181 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_181 :
    recurrence5B2A2.coeff 181 =
      ((((28175468336039417 * 10 ^ 70 +
        0408821779424850221945510476760599950775069196504681172392536752226617) * 10 ^ 70 +
        2231133232727621259486568996483081311897908701647848048346731268191499) * 10 ^ 70 +
        8019992642458285251271193286188107763846452368548341257471909802638776) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 182 = 13 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
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
    rw [show 41 = 5 +
      36 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_181_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_181_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_182_prefix_zero :
    (∑ x ∈ Finset.range 14,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (182 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (182 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_182_suffix_zero :
    (∑ x ∈ Finset.range 37,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (182 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_182 :
    recurrence5B2A2.coeff 182 =
      -((((23532590006915416 * 10 ^ 70 +
        8282622254370351190543361001254327820514600665018060174303627043451058) * 10 ^ 70 +
        6047276516296380146577580932037938235815422981889535339910598080748964) * 10 ^ 70 +
        2385447735412950674031005017202770291631707285517572494423386187879712) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 183 = 14 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
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
    rw [show 41 = 4 +
      37 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_182_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_182_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_183_prefix_zero :
    (∑ x ∈ Finset.range 15,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (183 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (183 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_183_suffix_zero :
    (∑ x ∈ Finset.range 38,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (183 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_183 :
    recurrence5B2A2.coeff 183 =
      ((((17708112997518063 * 10 ^ 70 +
        2521992783973019469747697419699115583717258394828711110367235403522402) * 10 ^ 70 +
        8139779473110882491554123235147770139244791773797619154794278978238139) * 10 ^ 70 +
        3162710159654397279133251286290084332721843438598991900399485901444982) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 184 = 15 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
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
    rw [show 41 = 3 +
      38 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_183_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_183_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_184_prefix_zero :
    (∑ x ∈ Finset.range 16,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (184 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (184 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_184_suffix_zero :
    (∑ x ∈ Finset.range 39,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (184 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_184 :
    recurrence5B2A2.coeff 184 =
      -((((12300755274771914 * 10 ^ 70 +
        0773549778073779754782156440503565832839496730514381348443784341132046) * 10 ^ 70 +
        5202030591022399759534305826521551862384867722740679954276815087900606) * 10 ^ 70 +
        5532253652458754273339951555036255059972869829010510017505298246932055) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 185 = 16 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
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
    rw [show 41 = 2 +
      39 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_184_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_184_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_185_prefix_zero :
    (∑ x ∈ Finset.range 17,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (185 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (185 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_185_suffix_zero :
    (∑ x ∈ Finset.range 40,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (185 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_185 :
    recurrence5B2A2.coeff 185 =
      ((((7986123934412801 * 10 ^ 70 +
        5249809862509781274820046353052095991970048982332784069415133010532798) * 10 ^ 70 +
        2694864182723050885246666739863689537466730212519680683835568115200714) * 10 ^ 70 +
        8116051061763147361838889201248450642582697522068413617438387485387956) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 186 = 17 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
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
    rw [show 41 = 1 +
      40 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_185_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_185_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_186_prefix_zero :
    (∑ x ∈ Finset.range 18,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (186 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (186 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_186_suffix_zero :
    (∑ x ∈ Finset.range 41,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (186 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_186 :
    recurrence5B2A2.coeff 186 =
      -((((4876981231128202 * 10 ^ 70 +
        7952229015421207882351175623568758903257908162667346914670316602827589) * 10 ^ 70 +
        6413256610186174375837756533637923218984987949806831955773195847844193) * 10 ^ 70 +
        9066441165026698262478225729809739034994035324907728541086245391697088) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 187 = 18 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 32 +
      73 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 73 = 32 +
      41 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_186_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_186_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_187_prefix_zero :
    (∑ x ∈ Finset.range 19,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (187 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (187 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_187_suffix_zero :
    (∑ x ∈ Finset.range 42,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (187 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_187 :
    recurrence5B2A2.coeff 187 =
      ((((2808416905908046 * 10 ^ 70 +
        8046504023116676255196032412800884678091942562677980129484715740990676) * 10 ^ 70 +
        7416230599115222567201322978879920914665215457437085063373562337025768) * 10 ^ 70 +
        0811081449573121192706320895476252048567168727801157233928413668937047) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 188 = 19 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 32 +
      73 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 73 = 31 +
      42 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_187_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_187_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_188_prefix_zero :
    (∑ x ∈ Finset.range 20,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (188 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (188 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_188_suffix_zero :
    (∑ x ∈ Finset.range 43,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (188 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_188 :
    recurrence5B2A2.coeff 188 =
      -((((1523782745061185 * 10 ^ 70 +
        9433752033819035189544732442045598987449626892072162656134198950263142) * 10 ^ 70 +
        1171343845806203372916661914849100038830618295896153527119081972415592) * 10 ^ 70 +
        5968915934789675641199844395496615101097762621006015636170615901357522) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 189 = 20 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 32 +
      73 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 73 = 30 +
      43 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_188_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_188_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_189_prefix_zero :
    (∑ x ∈ Finset.range 21,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (189 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (189 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_189_suffix_zero :
    (∑ x ∈ Finset.range 44,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (189 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_189 :
    recurrence5B2A2.coeff 189 =
      ((((775373658596855 * 10 ^ 70 +
        9911840754142006586886974561506533734936350496948348734126450448534224) * 10 ^ 70 +
        4879065328683247276595111058831938366689665278414041016531213929449175) * 10 ^ 70 +
        3024824872050628420569710902336750971768625429696690718100555454605231) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 190 = 21 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 32 +
      73 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 73 = 29 +
      44 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_189_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_189_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_190_prefix_zero :
    (∑ x ∈ Finset.range 22,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (190 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (190 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_190_suffix_zero :
    (∑ x ∈ Finset.range 45,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (190 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_190 :
    recurrence5B2A2.coeff 190 =
      -((((366045271063706 * 10 ^ 70 +
        5301614061242744641284347227785795795761830507644429864571573338555997) * 10 ^ 70 +
        1840970003739199195163098367878677565943049849155421751501237048622024) * 10 ^ 70 +
        1623091265252511717082588382661612775268510260197174332731456574732715) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 191 = 22 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 32 +
      73 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 73 = 28 +
      45 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_190_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_190_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_191_prefix_zero :
    (∑ x ∈ Finset.range 23,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (191 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (191 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_191_suffix_zero :
    (∑ x ∈ Finset.range 46,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (191 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_191 :
    recurrence5B2A2.coeff 191 =
      ((((156620874784390 * 10 ^ 70 +
        9016221990547509264601205227270591153530240910975066833534297209985692) * 10 ^ 70 +
        9710033654988713955934391982885375041136464949505724803401496844429839) * 10 ^ 70 +
        9159442614766484171980632079913036591655392104515898400354267888491316) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 192 = 23 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 32 +
      73 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 73 = 27 +
      46 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_191_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_191_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_192_prefix_zero :
    (∑ x ∈ Finset.range 24,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (192 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (192 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_192_suffix_zero :
    (∑ x ∈ Finset.range 47,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (192 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_192 :
    recurrence5B2A2.coeff 192 =
      -((((57372470679003 * 10 ^ 70 +
        2416168296729820651261964451492616813862137978036865452076478162617708) * 10 ^ 70 +
        6545817133343137779682736355570759697194100980928270331156407461049928) * 10 ^ 70 +
        5960830632825832706977038240657468728869755955259101914024984417061622) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 193 = 24 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 32 +
      73 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 73 = 26 +
      47 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_192_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_192_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_193_prefix_zero :
    (∑ x ∈ Finset.range 25,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (193 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (193 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_193_suffix_zero :
    (∑ x ∈ Finset.range 48,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (193 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_193 :
    recurrence5B2A2.coeff 193 =
      ((((14762980637724 * 10 ^ 70 +
        3343713799975189522870451094830888685915520098866014317899625181742772) * 10 ^ 70 +
        3520011419676396833255028866702593349702310952128460126895806051360532) * 10 ^ 70 +
        1477783399893821138148406162745441194795509132802560732893089187053387) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 194 = 25 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 32 +
      73 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 73 = 25 +
      48 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_193_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_193_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_194_prefix_zero :
    (∑ x ∈ Finset.range 26,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (194 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (194 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_194_suffix_zero :
    (∑ x ∈ Finset.range 49,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (194 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_194 :
    recurrence5B2A2.coeff 194 =
      ((((926838118679 * 10 ^ 70 +
        1621674819103230374755103664286570166602661395866507812698649584654396) * 10 ^ 70 +
        9584923818633413829397011021871893820681356701189292774437247383289234) * 10 ^ 70 +
        2342079103814933796231213413454027666060723892955486915028822046658859) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 195 = 26 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 32 +
      73 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 73 = 24 +
      49 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_194_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_194_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_195_prefix_zero :
    (∑ x ∈ Finset.range 27,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (195 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (195 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_195_suffix_zero :
    (∑ x ∈ Finset.range 50,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (195 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_195 :
    recurrence5B2A2.coeff 195 =
      -((((5035049523063 * 10 ^ 70 +
        1474860024413424603842087335248576294967666574590648883891570087915775) * 10 ^ 70 +
        7318264782397813862634219158046881375015279347019878261005697325216254) * 10 ^ 70 +
        2168828615133992396623799194597021793467863711219934040543346736411148) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 196 = 27 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 32 +
      73 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 73 = 23 +
      50 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_195_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_195_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_196_prefix_zero :
    (∑ x ∈ Finset.range 28,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (196 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (196 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_196_suffix_zero :
    (∑ x ∈ Finset.range 51,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (196 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_196 :
    recurrence5B2A2.coeff 196 =
      ((((4864820857674 * 10 ^ 70 +
        6327304163678910930840768752712778830569294996242874437043771817210953) * 10 ^ 70 +
        0339621201133139452459554971700744231942362263220073707047708715924132) * 10 ^ 70 +
        5802156161962280106284987662071833217422306685595531125214208915501995) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 197 = 28 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 32 +
      73 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 73 = 22 +
      51 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_196_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_196_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_197_prefix_zero :
    (∑ x ∈ Finset.range 29,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (197 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (197 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_197_suffix_zero :
    (∑ x ∈ Finset.range 52,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (197 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_197 :
    recurrence5B2A2.coeff 197 =
      -((((3560575761375 * 10 ^ 70 +
        7545061087900235785769878228088506705780721327117179384816418173367554) * 10 ^ 70 +
        4205044426375571952654741274067606809630762956620856171555515715847019) * 10 ^ 70 +
        4791365462502584151467692514997027856711436046255517712090669019800738) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 198 = 29 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 32 +
      73 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 73 = 21 +
      52 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_197_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_197_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_198_prefix_zero :
    (∑ x ∈ Finset.range 30,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (198 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (198 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_198_suffix_zero :
    (∑ x ∈ Finset.range 53,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (198 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_198 :
    recurrence5B2A2.coeff 198 =
      ((((2285443885359 * 10 ^ 70 +
        1762474966093986580299110903944119314328033123873830611305258297268661) * 10 ^ 70 +
        4233497518293514374722219822122315830883016332722816895649629014807353) * 10 ^ 70 +
        0382675709912755159841400163228343243188582750891626305187140171034073) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 199 = 30 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 32 +
      73 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 73 = 20 +
      53 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_198_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_198_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_199_prefix_zero :
    (∑ x ∈ Finset.range 31,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (199 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (199 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_199_suffix_zero :
    (∑ x ∈ Finset.range 54,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (199 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_199 :
    recurrence5B2A2.coeff 199 =
      -((((1350066374832 * 10 ^ 70 +
        7672537792436582192859047736791132790271442941319577955045291634721438) * 10 ^ 70 +
        0157784987479396921611796024843090884561934548619849347534723239275373) * 10 ^ 70 +
        8670323835419176116819483478678153409717478082524861330173415916333374) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 200 = 31 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 32 +
      73 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 73 = 19 +
      54 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_199_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_199_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_200_prefix_zero :
    (∑ x ∈ Finset.range 32,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (200 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (200 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_200_suffix_zero :
    (∑ x ∈ Finset.range 55,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (200 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_200 :
    recurrence5B2A2.coeff 200 =
      ((((749922265896 * 10 ^ 70 +
        9783972970695111304254912848725586565197430397697088562423816467998835) * 10 ^ 70 +
        0520111662090799646391436188744130063445416488685685217166503441227861) * 10 ^ 70 +
        6409720475696111438985726455109617124958214022755972043675781487353178) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 201 = 32 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 32 +
      73 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 73 = 18 +
      55 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_200_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_200_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_201_prefix_zero :
    (∑ x ∈ Finset.range 33,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (201 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (201 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_201_suffix_zero :
    (∑ x ∈ Finset.range 56,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (201 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_201 :
    recurrence5B2A2.coeff 201 =
      -((((396021321552 * 10 ^ 70 +
        1624090457182165553956083876418317270398298034044260263432844285826823) * 10 ^ 70 +
        2794185737729759182602568941460854706630484735302649805436241223177686) * 10 ^ 70 +
        6659572754505534257571857390359795994730261625917042633039003725318669) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 202 = 33 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 32 +
      73 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 73 = 17 +
      56 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_201_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_201_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_202_prefix_zero :
    (∑ x ∈ Finset.range 34,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (202 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (202 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_202_suffix_zero :
    (∑ x ∈ Finset.range 57,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (202 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_202 :
    recurrence5B2A2.coeff 202 =
      ((((199990934371 * 10 ^ 70 +
        8579816350872286951759798621605796316406549031729708043528874202864449) * 10 ^ 70 +
        4745833928512846770010525194796090749784892284005732015871147316829103) * 10 ^ 70 +
        0023867833522789702960292143609296208705288693823292634757039171965696) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 203 = 34 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 32 +
      73 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 73 = 16 +
      57 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_202_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_202_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_203_prefix_zero :
    (∑ x ∈ Finset.range 35,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (203 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (203 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_203_suffix_zero :
    (∑ x ∈ Finset.range 58,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (203 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_203 :
    recurrence5B2A2.coeff 203 =
      -((((96882200578 * 10 ^ 70 +
        1588918730944041244007279853872088409822822109015258322463977767522818) * 10 ^ 70 +
        7883769683144272853536884451595000466664655094818719675143105915046049) * 10 ^ 70 +
        8021148991779649773642155302913710018949845551588333108232548742923743) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 204 = 35 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 32 +
      73 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 73 = 15 +
      58 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_203_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_203_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_204_prefix_zero :
    (∑ x ∈ Finset.range 36,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (204 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (204 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_204_suffix_zero :
    (∑ x ∈ Finset.range 59,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (204 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_204 :
    recurrence5B2A2.coeff 204 =
      ((((45095998087 * 10 ^ 70 +
        0654748396423518033346466196690611842800797616266267939186082308904772) * 10 ^ 70 +
        5499466148741165790830781361562348614372183599587019800247887846757014) * 10 ^ 70 +
        7612416783437328958204734009797349341006926232938132145353026717908192) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 205 = 36 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 32 +
      73 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 73 = 14 +
      59 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_204_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_204_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_205_prefix_zero :
    (∑ x ∈ Finset.range 37,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (205 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (205 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_205_suffix_zero :
    (∑ x ∈ Finset.range 60,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (205 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_205 :
    recurrence5B2A2.coeff 205 =
      -((((20193090205 * 10 ^ 70 +
        9208895522717874912979048111147950454846780190784841966338988894897220) * 10 ^ 70 +
        5869393619631180568804511301295304792567301628614154239290395106369332) * 10 ^ 70 +
        7049003293205371672248278203885701581168037793485604457247946827500219) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 206 = 37 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 32 +
      73 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 73 = 13 +
      60 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_205_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_205_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_206_prefix_zero :
    (∑ x ∈ Finset.range 38,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (206 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (206 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_206_suffix_zero :
    (∑ x ∈ Finset.range 61,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (206 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_206 :
    recurrence5B2A2.coeff 206 =
      ((((8713958196 * 10 ^ 70 +
        0581956740052625359952754917729140405485645055254408877398505563101758) * 10 ^ 70 +
        2173552878437949450461707740018559338921840817261889034886811208629170) * 10 ^ 70 +
        8126957807415872661385241445718514604885262727524511206037522136101982) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 207 = 38 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 32 +
      73 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 73 = 12 +
      61 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_206_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_206_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_207_prefix_zero :
    (∑ x ∈ Finset.range 39,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (207 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (207 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_207_suffix_zero :
    (∑ x ∈ Finset.range 62,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (207 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_207 :
    recurrence5B2A2.coeff 207 =
      -((((3638451110 * 10 ^ 70 +
        3819455266539707516798397339704652339835330941538523877611180433967520) * 10 ^ 70 +
        6992410071625239835097269615894249924302758316029008937250565493234207) * 10 ^ 70 +
        8686810411685391803559347850045438520959714540909637903155528682198568) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 208 = 39 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 32 +
      73 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 73 = 11 +
      62 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_207_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_207_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_208_prefix_zero :
    (∑ x ∈ Finset.range 40,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (208 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (208 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_208_suffix_zero :
    (∑ x ∈ Finset.range 63,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (208 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_208 :
    recurrence5B2A2.coeff 208 =
      ((((1482901119 * 10 ^ 70 +
        5137307402736299368543665082945612562626578471194868887241116199479477) * 10 ^ 70 +
        2052603951684510479126473946245244916554986996681441003194127260621842) * 10 ^ 70 +
        7816264802055906542050791941865869239166911129980050116987879370630395) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 209 = 40 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 32 +
      73 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 73 = 10 +
      63 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_208_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_208_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_209_prefix_zero :
    (∑ x ∈ Finset.range 41,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (209 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (209 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_209_suffix_zero :
    (∑ x ∈ Finset.range 64,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (209 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_209 :
    recurrence5B2A2.coeff 209 =
      -((((600059408 * 10 ^ 70 +
        5848271850398435053496476615168691271615181726817267632813999624266358) * 10 ^ 70 +
        0297701987511513011579325393703619461875905110675277256845053283412505) * 10 ^ 70 +
        5246642838529942840676069711941935529813903246094526564449316495341999) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 210 = 41 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 32 +
      73 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 73 = 9 +
      64 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_209_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_209_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_210_prefix_zero :
    (∑ x ∈ Finset.range 42,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (210 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (210 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_210_suffix_zero :
    (∑ x ∈ Finset.range 65,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (210 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_210 :
    recurrence5B2A2.coeff 210 =
      ((((247885641 * 10 ^ 70 +
        9047867546805332994879224618090751018174572422910416851581088829199894) * 10 ^ 70 +
        2961797582109563226375258582845993096419924721730301369008603848163704) * 10 ^ 70 +
        4672558445610376012476183600778930013102150244791162591336273626174565) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 211 = 42 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 32 +
      73 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 73 = 8 +
      65 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_210_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_210_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_211_prefix_zero :
    (∑ x ∈ Finset.range 43,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (211 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (211 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_211_suffix_zero :
    (∑ x ∈ Finset.range 66,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (211 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_211 :
    recurrence5B2A2.coeff 211 =
      -((((108198585 * 10 ^ 70 +
        4003513648956427930146443826751983978189205376952784381040250050419839) * 10 ^ 70 +
        8475569976969962023767348878010026922573292061324912730316205389774537) * 10 ^ 70 +
        3388779969689048403539736180439595049427997443686813936792304393693873) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 212 = 43 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 32 +
      73 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 73 = 7 +
      66 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_211_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_211_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_212_prefix_zero :
    (∑ x ∈ Finset.range 44,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (212 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (212 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_212_suffix_zero :
    (∑ x ∈ Finset.range 67,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (212 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_212 :
    recurrence5B2A2.coeff 212 =
      ((((51140293 * 10 ^ 70 +
        4149118097948932432832327017549686514277583219826746698516741339361305) * 10 ^ 70 +
        3368086344791214124663446929677417781867886641075176839108901477476686) * 10 ^ 70 +
        6989496318166930397895778822350987147682781117119296155799576475318553) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 213 = 44 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 32 +
      73 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 73 = 6 +
      67 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_212_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_212_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_213_prefix_zero :
    (∑ x ∈ Finset.range 45,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (213 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (213 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_213_suffix_zero :
    (∑ x ∈ Finset.range 68,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (213 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_213 :
    recurrence5B2A2.coeff 213 =
      -((((26093137 * 10 ^ 70 +
        8028767684640936788405204868071664462923179748677733855849546993454635) * 10 ^ 70 +
        5927814075767490002579851450062927423310875535901162097919120669935275) * 10 ^ 70 +
        8882754949640865374790576925316127938909058233172508967894973067251441) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 214 = 45 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 32 +
      73 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 73 = 5 +
      68 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_213_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_213_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_214_prefix_zero :
    (∑ x ∈ Finset.range 46,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (214 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (214 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_214_suffix_zero :
    (∑ x ∈ Finset.range 69,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (214 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_214 :
    recurrence5B2A2.coeff 214 =
      ((((13972647 * 10 ^ 70 +
        3331651994033822976802760675330865757762094294773313530415375763413547) * 10 ^ 70 +
        1576685413445754622211718820879015842857802038321700159529143876460966) * 10 ^ 70 +
        7225603812760674547331437989580047148200499731917196846175080924964609) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 215 = 46 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 32 +
      73 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 73 = 4 +
      69 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_214_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_214_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_215_prefix_zero :
    (∑ x ∈ Finset.range 47,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (215 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (215 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_215_suffix_zero :
    (∑ x ∈ Finset.range 70,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (215 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_215 :
    recurrence5B2A2.coeff 215 =
      -((((7591928 * 10 ^ 70 +
        9112224572006329232883775314492392905557961267431999048466133774639442) * 10 ^ 70 +
        2988904043615760646735377572415698823299100763830011049508520295902461) * 10 ^ 70 +
        1420432701814508840683762637050945521920433467329862011379611187404063) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 216 = 47 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 32 +
      73 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 73 = 3 +
      70 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_215_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_215_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_216_prefix_zero :
    (∑ x ∈ Finset.range 48,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (216 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (216 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_216_suffix_zero :
    (∑ x ∈ Finset.range 71,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (216 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_216 :
    recurrence5B2A2.coeff 216 =
      ((((4080720 * 10 ^ 70 +
        4635169006861128124330566316879262231981660277696960630579444277720180) * 10 ^ 70 +
        9957254030079069876849123707152713540184228442859854050941780808763342) * 10 ^ 70 +
        8535979515447568265146109180827767383075720355937129235507743509529618) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 217 = 48 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 32 +
      73 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 73 = 2 +
      71 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_216_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_216_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_217_prefix_zero :
    (∑ x ∈ Finset.range 49,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (217 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (217 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_217_suffix_zero :
    (∑ x ∈ Finset.range 72,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (217 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_217 :
    recurrence5B2A2.coeff 217 =
      -((((2138209 * 10 ^ 70 +
        9650294636940918179219992111564715796039557231636253725608273810935978) * 10 ^ 70 +
        9244322056940981662461603325221450532174962909634222414764452769423703) * 10 ^ 70 +
        1199027910198775580765507764122974548575544959341441737257852466537079) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 218 = 49 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 32 +
      73 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 73 = 1 +
      72 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_217_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_217_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A2_coeff_218_prefix_zero :
    (∑ x ∈ Finset.range 50,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (218 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (218 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_218_suffix_zero :
    (∑ x ∈ Finset.range 73,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (218 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_218 :
    recurrence5B2A2.coeff 218 =
      ((((1084478 * 10 ^ 70 +
        8390634276571582110446119613246659977137250091826670798989827898350256) * 10 ^ 70 +
        0601515074645328491605291287255157739805954603256811799323215994006974) * 10 ^ 70 +
        2851893576141108519636235154487074467623267124670294770444037193121103) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 219 = 50 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 32 +
      73 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_218_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_218_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
