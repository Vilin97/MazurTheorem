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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
