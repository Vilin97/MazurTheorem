/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupB2
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupLeadingSquarePart0Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 5 lookup certificate: LeadingSquare coefficient convolution

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

theorem recurrence5LeadingSquare_coeff_69 :
    recurrence5LeadingSquare.coeff 69 =
      -((((14194837342797823048438 * 10 ^ 70 +
        6233222522616093170854710154394354875927953420857054181584521408871942) * 10 ^ 70 +
        8001178309836296322717619688394370861705943743133574863994285305442214) * 10 ^ 70 +
        3638086196639205197463608047458551395178166795641170322096431207267630) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_70 :
    recurrence5LeadingSquare.coeff 70 =
      ((((91663074633856205458317 * 10 ^ 70 +
        6480154983474418109806210535866145112256396749373579258866989552336191) * 10 ^ 70 +
        7094328715898689473226577985005444921698398744400311421144980505266770) * 10 ^ 70 +
        4929168479113043227809261327718681632998198480980001702599662511169164) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_71 :
    recurrence5LeadingSquare.coeff 71 =
      -((((567752753582510221319769 * 10 ^ 70 +
        6540706643106362168468363705634929646838744840557618292619222508683883) * 10 ^ 70 +
        2938641545274151911430285049557128387180979797347569377005437479423741) * 10 ^ 70 +
        9460053977663830923503965758644011744856768915690206947964073089232888) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_72 :
    recurrence5LeadingSquare.coeff 72 =
      ((((3374876230383669052243588 * 10 ^ 70 +
        2454666707593284991171268447970072441779888080893949580812573988577874) * 10 ^ 70 +
        9575100834562480685481752966869879757499513763797500224874894159523968) * 10 ^ 70 +
        3957363616569189316646265857491491876963723082999486458107627028385953) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_73 :
    recurrence5LeadingSquare.coeff 73 =
      -((((19262683820989029111864917 * 10 ^ 70 +
        2560012585665390788340318789652361382204802840378951487205716008526820) * 10 ^ 70 +
        1081426710560440032470427587624000382972792300045310516610813775444287) * 10 ^ 70 +
        7952575847998268061759972837837661550053006943050434539545255997493296) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_74 :
    recurrence5LeadingSquare.coeff 74 =
      ((((105622506094487409425814516 * 10 ^ 70 +
        8933832358989449069975996618149018243367174771424056135819808489125574) * 10 ^ 70 +
        2504799072509710991841024731759198303620186335804886037644178677793933) * 10 ^ 70 +
        1266458736265432176952665222147496003810917062736564367095276959739984) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_75 :
    recurrence5LeadingSquare.coeff 75 =
      -((((556661549280200368678626347 * 10 ^ 70 +
        4514070289957655223398339226260862091894661233429762189442679986859509) * 10 ^ 70 +
        2923040708166752421052981380337542624381791378259123620646830128417157) * 10 ^ 70 +
        9392723438097359688039999268536477001417446641322988128641883359273452) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_76 :
    recurrence5LeadingSquare.coeff 76 =
      ((((2821171992322232944662513644 * 10 ^ 70 +
        4060542487325637940731746718209164096438914445378660788765689971010416) * 10 ^ 70 +
        1184375251308660438943960462947160927042455772533464709824151158540152) * 10 ^ 70 +
        2331310660717147064616933375208785756870935633221846875855075597337873) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_77 :
    recurrence5LeadingSquare.coeff 77 =
      -((((13755433412427696917266709826 * 10 ^ 70 +
        3621333589952482977562759969933721664478583656451048277812160779101368) * 10 ^ 70 +
        6805532988802464689310006867270352006222913144026999741039232268736340) * 10 ^ 70 +
        6533124190921622176216198029888481104323805441393421801602188150556850) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_78 :
    recurrence5LeadingSquare.coeff 78 =
      ((((64553917301452703310488136823 * 10 ^ 70 +
        6925610841375826444947962694588840321301891137642078613989092437747557) * 10 ^ 70 +
        5439853404108569946078405603128642043654437097297841293866923277599076) * 10 ^ 70 +
        7171099842856225035335615221861989274706400941506442776015978884001100) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_79 :
    recurrence5LeadingSquare.coeff 79 =
      -((((291720092824281595754378091133 * 10 ^ 70 +
        3459848842280531983985362977251941534639632146306271888807126713014089) * 10 ^ 70 +
        4441824722651984093027768465384301474538109727059416120825130256667008) * 10 ^ 70 +
        9642397969812148712839846844965135947884932192898631133145848601032936) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_80 :
    recurrence5LeadingSquare.coeff 80 =
      ((((1269965808446724158560246646979 * 10 ^ 70 +
        8950691156727536050129923231594119912002822218699151803426039018707156) * 10 ^ 70 +
        0442020952399228865476255998129295997080116134188976694445455502895920) * 10 ^ 70 +
        3691422001963664436471570203098761182161933264763057463693450901171696) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_81 :
    recurrence5LeadingSquare.coeff 81 =
      -((((5328206213442624828842397234993 * 10 ^ 70 +
        1156032853851048002033554249194779017371026044735488884238471003898344) * 10 ^ 70 +
        1346505675896568957347656789644019166463016180582400255054448306443687) * 10 ^ 70 +
        2513346731717147964408451207470213242134785419115524925307620622600378) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_82 :
    recurrence5LeadingSquare.coeff 82 =
      ((((21553096005990799175067966456380 * 10 ^ 70 +
        4077586281266793985434112562002043394471897470753771314257614949150713) * 10 ^ 70 +
        5870116015466631597744335172731479475009166965985134847679936879326722) * 10 ^ 70 +
        7880624523705657368502979639255340724390070841485490790251437153214875) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_83 :
    recurrence5LeadingSquare.coeff 83 =
      -((((84090969683144754358807582164413 * 10 ^ 70 +
        1621379111989379603530265861704348143637757725882958199299790057962430) * 10 ^ 70 +
        3129538071706931991216102780664542473558957086403419352158596991985141) * 10 ^ 70 +
        6363047369268508673164555547433645211898079608986894991576192710179918) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_84 :
    recurrence5LeadingSquare.coeff 84 =
      ((((316567793655075998019197728867759 * 10 ^ 70 +
        9383706659792134400335716162083447284112482862722452012901026720291037) * 10 ^ 70 +
        8321148198443081816807012521173516128680776196685700431940434171982550) * 10 ^ 70 +
        6690270784437632710238967708461995859143249142155332591480690841992485) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_85 :
    recurrence5LeadingSquare.coeff 85 =
      -((((1150333298866091641045293340557320 * 10 ^ 70 +
        6788333559191118444847924722803092030904822694036823208696149923225891) * 10 ^ 70 +
        4895951499731815548935448931431427696333741356450411188202129998316953) * 10 ^ 70 +
        3578224402328705393456391611272845506470666534283195345020379471303136) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_86 :
    recurrence5LeadingSquare.coeff 86 =
      ((((4036245583549093842122265487504169 * 10 ^ 70 +
        9533655620070038384005724724065302386523681327826317733946772113654546) * 10 ^ 70 +
        8263561447105062448686527333488087706220452407302773016601580326529883) * 10 ^ 70 +
        7460768218342762875529949742628733205942799042070918912809994348191098) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_87 :
    recurrence5LeadingSquare.coeff 87 =
      -((((13679847497661949966987753898331342 * 10 ^ 70 +
        0090814083970944260213544632277989131252248810306371829206022163252436) * 10 ^ 70 +
        8182633494221694194703215119792275850497276647930945063468180373741960) * 10 ^ 70 +
        8661214088437324581884042762057092236218762656965334800849319281393100) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_88 :
    recurrence5LeadingSquare.coeff 88 =
      ((((44800532886978420721719571322746181 * 10 ^ 70 +
        0258566533827673537386155482184732217658229794278119816293489240308857) * 10 ^ 70 +
        4282460457399564226178839581482625015704922908805900264615901505065550) * 10 ^ 70 +
        3856268268570391528240012086307142134503589857884466547802109001665911) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_89 :
    recurrence5LeadingSquare.coeff 89 =
      -((((141816752374406148839965543415675549 * 10 ^ 70 +
        1901973818187493126013285070199230640158691640230117736924631068920792) * 10 ^ 70 +
        7360304412045210130793810507848917217384542839896508010315751497289433) * 10 ^ 70 +
        2679780635292453374432029872687330586642981370875144443909446381769304) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_90 :
    recurrence5LeadingSquare.coeff 90 =
      ((((434064541608714759334176530560997846 * 10 ^ 70 +
        2499241934371987125214768804782261091528251359580119118231168262516934) * 10 ^ 70 +
        3836702332656126685754043273673756931859925025651498559272749133755527) * 10 ^ 70 +
        3394600687867862600912373407989414155218225510022438662032915871556589) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_91 :
    recurrence5LeadingSquare.coeff 91 =
      -((((1284988924611530357335609813034687476 * 10 ^ 70 +
        1102362301401763372826224723499866069913937508641641863014742779988521) * 10 ^ 70 +
        6899131508650231779444396434312210164258510345381624677998609897190747) * 10 ^ 70 +
        7929575550945308162762525583538410644581515216924467785099704630250560) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_92 :
    recurrence5LeadingSquare.coeff 92 =
      ((((3680396615088756119468785991073455474 * 10 ^ 70 +
        4980999717437697721504005183695988838190656299329951352108576989926138) * 10 ^ 70 +
        7683819188321729136298412398498547087995535840300207629754486835754450) * 10 ^ 70 +
        3747232586580284730320597559716420707455798441063769358595977610264923) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_93 :
    recurrence5LeadingSquare.coeff 93 =
      -((((10201592101517156802309987629921905612 * 10 ^ 70 +
        4225447645705122341670394650473559591063575101613181065109237059563382) * 10 ^ 70 +
        9889046089310071367304036226765722283169411751367149276154355961570231) * 10 ^ 70 +
        3533498016262065244906755822729168219510782625543766744927324130870904) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_94 :
    recurrence5LeadingSquare.coeff 94 =
      ((((27374327546032347510199312202365185096 * 10 ^ 70 +
        7068907484036308024110161760015344841598698008282851849808387600721825) * 10 ^ 70 +
        4986085389685906354035851632167312455438150545274623957194622855082842) * 10 ^ 70 +
        2838336888768887666216159927383852127661221326223085559080144068905140) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_95 :
    recurrence5LeadingSquare.coeff 95 =
      -((((71128138378753028491012365863596452743 * 10 ^ 70 +
        2499173019220206921052174976309268973310228052346120462871315882040920) * 10 ^ 70 +
        8051426817316782476649338012747102413422859893261936464341097433068663) * 10 ^ 70 +
        7660775875227438310371855815402911714841970507760766537105611596877758) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_96 :
    recurrence5LeadingSquare.coeff 96 =
      ((((179010502530703495479226375076561482915 * 10 ^ 70 +
        0751283882935654729768992743483857231377100355758819975275034048337897) * 10 ^ 70 +
        4813388593259208578635280785348411487380934726290767538844322762088575) * 10 ^ 70 +
        0723609183992557845842399307378949026297810799914402280973418197302818) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_97 :
    recurrence5LeadingSquare.coeff 97 =
      -((((436483322415874574660981611350711035486 * 10 ^ 70 +
        2478831393970579234854736562127789637560211842133922139107167966344963) * 10 ^ 70 +
        7028339035512137771696596381277868860030567424816142629325016378232128) * 10 ^ 70 +
        1436616350377607737210900064642359633732728105284423938753909033682216) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_98 :
    recurrence5LeadingSquare.coeff 98 =
      ((((1031379048183053673285199914198294984166 * 10 ^ 70 +
        2865502385826249714962065107655111845977647113788981858771260442844674) * 10 ^ 70 +
        7795221523623537539534597189084492935087927747970443920552469131704614) * 10 ^ 70 +
        1082200484417760482341876693430773507339253061389704254882466689801776) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_99 :
    recurrence5LeadingSquare.coeff 99 =
      -((((2362307422520736184905515152626471762602 * 10 ^ 70 +
        3485521678767771086600599039058536573370648954272905318808886803618506) * 10 ^ 70 +
        4606522678604870456372608737622424459917493931371935632246786413659139) * 10 ^ 70 +
        9445616292068691369739341606620335346880603116937211118791362264763494) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_100 :
    recurrence5LeadingSquare.coeff 100 =
      ((((5245954493858016937334211156723800395194 * 10 ^ 70 +
        5183250697081959510556420105287938660310109839414765854275916796979043) * 10 ^ 70 +
        9225748757640563245001813689953790676549056877604132580633791104102729) * 10 ^ 70 +
        0444432839169886773070624109612960389043972089748433439870879508525941) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_101 :
    recurrence5LeadingSquare.coeff 101 =
      -((((11297485699854051934853703308254313019911 * 10 ^ 70 +
        6921324074966325669521907688517082843520414475162912969857250364457057) * 10 ^ 70 +
        8928675584882858077145492932170905067963992838925946198888885113393931) * 10 ^ 70 +
        2731367674195327260374040778663828720804595375662180385670095121102124) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_102 :
    recurrence5LeadingSquare.coeff 102 =
      ((((23599573204221086567677776070856468922237 * 10 ^ 70 +
        4346024984506535149262620247023540799458858376031389951267197332058122) * 10 ^ 70 +
        1256222876696505016705256510144567688337789356667947504765575152366804) * 10 ^ 70 +
        6227052803102764577362589725560367273916251523795837346635067090934069) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_103 :
    recurrence5LeadingSquare.coeff 103 =
      -((((47828220400487037925630716833140131185210 * 10 ^ 70 +
        9987506085144658567322721925134533091963313118279616372102234878131402) * 10 ^ 70 +
        1921857799121795519483598447848976180031834546621807791592404450653266) * 10 ^ 70 +
        0577602686606769939181118973496311978820041056506570543954912651361750) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_104 :
    recurrence5LeadingSquare.coeff 104 =
      ((((94061413133246537846657217472153222636402 * 10 ^ 70 +
        7990767638476593822303710681012955581630778849616116706444476999718793) * 10 ^ 70 +
        5980449019057654115860593794466520000672341386550988204643764581726263) * 10 ^ 70 +
        0187086185827498579012394344669735884904577406818096404148489491309769) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_105 :
    recurrence5LeadingSquare.coeff 105 =
      -((((179544595204692075784052696327032010387202 * 10 ^ 70 +
        0023445407096787804102944338649647487699219224757159027873130580752407) * 10 ^ 70 +
        8340881758354270457825541419190216607266937531978792813122790437404896) * 10 ^ 70 +
        3956679894554532104918364764836395478326776858275121138466133220886550) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_106 :
    recurrence5LeadingSquare.coeff 106 =
      ((((332697865981174834007411015632727877995480 * 10 ^ 70 +
        7620700707831078695318991973516795719469126563271230636698166858841015) * 10 ^ 70 +
        2981146191693635327044351112914989302067780864182250927059801554805707) * 10 ^ 70 +
        1336615800227910533040528592635318114699997131597086418805225466184115) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_107 :
    recurrence5LeadingSquare.coeff 107 =
      -((((598583570068328318408295994553592841874760 * 10 ^ 70 +
        9315812329834315647951019805031450136824334843016364713789632480364706) * 10 ^ 70 +
        5202946409524575904402089668934202122012789378916486982391922453942295) * 10 ^ 70 +
        3755614169504179617912838551381588303450398406993759428317693510054014) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_108 :
    recurrence5LeadingSquare.coeff 108 =
      ((((1045860935288361253946188506364065772805820 * 10 ^ 70 +
        3917833809665738219815275686105315997455855424109622413831350149313402) * 10 ^ 70 +
        8165758550939008431593154961086426711214174304089541284893803177998848) * 10 ^ 70 +
        9488080380669848119918688741720787720603018843234978806142538733326259) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_109 :
    recurrence5LeadingSquare.coeff 109 =
      -((((1774891453989023674833842803661454417797516 * 10 ^ 70 +
        0401514116886701056073928495966950694180572462236454008370417828746297) * 10 ^ 70 +
        4542214004881479728603108234386036820171629185562330147453581063124462) * 10 ^ 70 +
        8747534389258002234471392655583087082895541443870581500843501981180974) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_110 :
    recurrence5LeadingSquare.coeff 110 =
      ((((2926104248404459699666946189739858214705138 * 10 ^ 70 +
        6823834532574160366132129154433525622049642056168165386526263906515515) * 10 ^ 70 +
        6030188365711967326537978236266837077762362678029607142292098039307387) * 10 ^ 70 +
        6148857667302001746559992421476507916007286742088363037261380694387633) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_111 :
    recurrence5LeadingSquare.coeff 111 =
      -((((4687016642297289957594831454822222952205379 * 10 ^ 70 +
        2718706578609633298800734977341236091435857806590626320289276849074429) * 10 ^ 70 +
        6277658141892236547052380841932870850854069970119339261660931901907775) * 10 ^ 70 +
        6334971126762935700656121974704497288516660109605604734911024266527094) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_112 :
    recurrence5LeadingSquare.coeff 112 =
      ((((7295543109170153347325420677561619052442896 * 10 ^ 70 +
        6604650438878130281932764815548408577946646199625678991379997500146275) * 10 ^ 70 +
        8634765744984294293054193261062661559682219154127573318887661345738273) * 10 ^ 70 +
        8150406202721025413177492937997886328148258268397729862305384970050647) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_113 :
    recurrence5LeadingSquare.coeff 113 =
      -((((11036620430611285187998730998078209374994476 * 10 ^ 70 +
        4540040652268026835983829245156251931875230084442435075249948597670955) * 10 ^ 70 +
        8256639486039338960865284288586562022518244407238549849083272652367282) * 10 ^ 70 +
        7638442171912982474555824460478228592662923837150980306082803586920034) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_114 :
    recurrence5LeadingSquare.coeff 114 =
      ((((16229010946523516660500886947741925128388077 * 10 ^ 70 +
        9116381697484965536059068307741986177423618407570801585317951843821721) * 10 ^ 70 +
        2852305724110593033460495933614709290939415602200059407438683406312226) * 10 ^ 70 +
        0125426079161174236234210379423736223265043564411783220606252498201853) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_115 :
    recurrence5LeadingSquare.coeff 115 =
      -((((23199723546638122577133464548601712661299912 * 10 ^ 70 +
        5727493489403235658099707261431571694227412856304590142529845199415570) * 10 ^ 70 +
        9432296235632708158498298075286126366538098824089638590624965663583689) * 10 ^ 70 +
        5501937728548484586651930376735243164513950756555140685974128523393550) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_116 :
    recurrence5LeadingSquare.coeff 116 =
      ((((32245041742168606503550848553884911152208546 * 10 ^ 70 +
        3455214496549094255538798654168770901437763363002668332847048317938664) * 10 ^ 70 +
        9870839712102264852062385092765389928759861550499955050201824282356260) * 10 ^ 70 +
        8583409197622108611685969057439303441092827387005146540343411833501346) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_117 :
    recurrence5LeadingSquare.coeff 117 =
      -((((43579700465802297385426226871524256463577678 * 10 ^ 70 +
        6910168104317171227960270515197469548787294417208880923518984579545583) * 10 ^ 70 +
        5015201797750819501514336399444179345092358626755195482815388289346100) * 10 ^ 70 +
        4842034057562460726471786192445512053188498783385055667248551237396350) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_118 :
    recurrence5LeadingSquare.coeff 118 =
      ((((57279034538291278933931219309829717264409200 * 10 ^ 70 +
        8741045899891440965752001305177431637069148402895830485217556109128668) * 10 ^ 70 +
        9188904890755696991417937574028194977552749526750135677157504607878657) * 10 ^ 70 +
        3984642656416308396972686549800495634611199702735385853743185881864156) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_119 :
    recurrence5LeadingSquare.coeff 119 =
      -((((73222312290832984332180996413923127639519273 * 10 ^ 70 +
        0588799427859554521385531885380186886775327514822534950783044521011857) * 10 ^ 70 +
        5115060043634113124371858154260663712780153263261017186122886755911282) * 10 ^ 70 +
        2897676489012782797698894778177205783436768052279760682862947650204594) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_120 :
    recurrence5LeadingSquare.coeff 120 =
      ((((91048070551353010074971411880293912164870670 * 10 ^ 70 +
        0529398955340975085524104861768152841464759652092235154209738168257424) * 10 ^ 70 +
        4492721236544634158768875988152223371527022610820872117822195274897756) * 10 ^ 70 +
        1115411471944779499247237048506856940700474917319524863990920424814948) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_121 :
    recurrence5LeadingSquare.coeff 121 =
      -((((110133103979767617526396167978844546801644037 * 10 ^ 70 +
        6816311405015381061831906502465606397940996709476605577526827068695923) * 10 ^ 70 +
        6423105938189963396245552811644249492496518050227964365024624802085682) * 10 ^ 70 +
        2920732837848654535108073127582639000150082687979484712975410578825054) : ℚ) := by
  unfold recurrence5LeadingSquare
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

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
