/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupB2
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupA2
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupB2A2Part0Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 5 lookup certificate: B2A2 coefficient convolution

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
