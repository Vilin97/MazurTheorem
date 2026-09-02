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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
