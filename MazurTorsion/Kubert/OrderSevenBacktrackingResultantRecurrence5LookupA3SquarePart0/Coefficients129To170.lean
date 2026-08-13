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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
