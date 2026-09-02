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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
