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

theorem recurrence5LeadingSquare_coeff_122 :
    recurrence5LeadingSquare.coeff 122 =
      ((((129605067626788106107562152276019148226072608 * 10 ^ 70 +
        7676376028443077097060740611827341112563815100152568697543265171197199) * 10 ^ 70 +
        2633281363091429749048920443630583113699249522646834430338093456295880) * 10 ^ 70 +
        3538920543841765990015925494498312460747858639286009167203655361163341) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_123 :
    recurrence5LeadingSquare.coeff 123 =
      -((((148394186326300445355052758581293045441520315 * 10 ^ 70 +
        0253518052309560306038851650087001002422366357201215321972013012411809) * 10 ^ 70 +
        3311305095894211724255004797497941689114855753930684686184864353020756) * 10 ^ 70 +
        1987885948337511618124958026173761192625534956401510869340483122147956) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_124 :
    recurrence5LeadingSquare.coeff 124 =
      ((((165322828932800719419908433389757231511455154 * 10 ^ 70 +
        7277979564491780208709525763363614360544877633071240325927325874641536) * 10 ^ 70 +
        9904732679301193597184063115984002300783933462012498896912688424598227) * 10 ^ 70 +
        4854966403584294367168274184887166870579420525092089373989999147911909) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_125 :
    recurrence5LeadingSquare.coeff 125 =
      -((((179223957370904624858044348960621748345526483 * 10 ^ 70 +
        1240743821660776594111647294539243425089123274230074327730048325112856) * 10 ^ 70 +
        9423149059279135898596449172290653346117649353366399152734537774563032) * 10 ^ 70 +
        8968232696076246114912320972973693418341336197257092611405695722697264) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_126 :
    recurrence5LeadingSquare.coeff 126 =
      ((((189072478706326840920165007372457749190317576 * 10 ^ 70 +
        8769669509786894868092993238389288023841138653370291818144708079528432) * 10 ^ 70 +
        0776186475654818970677317166253924559124260737041126270313188946386241) * 10 ^ 70 +
        7300089961096289977412648542762340880096269644834786691002483085913082) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_127 :
    recurrence5LeadingSquare.coeff 127 =
      -((((194109159518572843180370639572637599150504418 * 10 ^ 70 +
        9912277232775313605730415336928765619788961822833471276483994434437589) * 10 ^ 70 +
        1471443642680610009185555868129775212730696995338228319312751843650221) * 10 ^ 70 +
        0278875185850803316769124531115917684592831842885857514805901692446732) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_128 :
    recurrence5LeadingSquare.coeff 128 =
      ((((193936375152811637472379457785821470842350516 * 10 ^ 70 +
        1744274028937728711163269932103326316974134762976355500054008119719478) * 10 ^ 70 +
        5686003928844077784752879388706213154565471973966000587633479281485160) * 10 ^ 70 +
        5958804828967494204840734460447105802912926220818059379571336014988185) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_129 :
    recurrence5LeadingSquare.coeff 129 =
      -((((188568995755303370900338030615713775130612195 * 10 ^ 70 +
        2720181895655325768083489268139910408259142100161962615081661696948602) * 10 ^ 70 +
        2000943571873341902590135780111409021428194033630342199865548867080583) * 10 ^ 70 +
        0832300016433431714541526972985584933836193586984705198814193775094600) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_130 :
    recurrence5LeadingSquare.coeff 130 =
      ((((178431450456711028079890014897546537035556942 * 10 ^ 70 +
        0481282588196120926641215260356617829286827694399768957643750507705000) * 10 ^ 70 +
        0292368530599372900264533569928200917058403763583085621499550347313906) * 10 ^ 70 +
        4053736591666946328132959063184438065430947147914881344923021977206058) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_131 :
    recurrence5LeadingSquare.coeff 131 =
      -((((164301755334427459149416738679885271663304998 * 10 ^ 70 +
        5065238531171136287667471651816707393862678231633712507894160178329977) * 10 ^ 70 +
        4143570274491215128054211574179644066064146779806865287516058665869186) * 10 ^ 70 +
        9930877885431294412875280662419639981027541615741555948788192957989920) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_132 :
    recurrence5LeadingSquare.coeff 132 =
      ((((147212790908979379553585113935161185762993643 * 10 ^ 70 +
        7572904819065102169987599999199733426634015946634278958709710777653294) * 10 ^ 70 +
        9581064879961425556773111457245605988331900249844382701808583512382182) * 10 ^ 70 +
        4878421557109082623303222212629093254898042020259549009532055821453375) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_133 :
    recurrence5LeadingSquare.coeff 133 =
      -((((128328206930385291172546479106243747159647173 * 10 ^ 70 +
        7365403329788083835824761751686936904778358522873202023649522243153731) * 10 ^ 70 +
        3060868177387138020808599185568298017179447130116329768325471380636306) * 10 ^ 70 +
        8785397768954599648915872615226718027101068611256865577168947618872200) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_134 :
    recurrence5LeadingSquare.coeff 134 =
      ((((108813532911996842710851896283024036138906863 * 10 ^ 70 +
        1908212318369778636653881203071921385123256738872649093970685567488706) * 10 ^ 70 +
        6010366394285168384858711137034524101520719568889007884420161115222630) * 10 ^ 70 +
        7969064180984958753912395734873916360716589183323987421401041896255347) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_135 :
    recurrence5LeadingSquare.coeff 135 =
      -((((89721951345247897599812436896625827747861920 * 10 ^ 70 +
        4584475349735587596198729212899914611777058441216126520755176384103298) * 10 ^ 70 +
        0682916949714791914457141709254582925272816904651260821292380409429203) * 10 ^ 70 +
        1577675907770070428379894603786886181742319184448575400386447173947920) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_136 :
    recurrence5LeadingSquare.coeff 136 =
      ((((71909407668202025034229712025628780809350618 * 10 ^ 70 +
        1279608096058988906833493680449286290314397051586280411941285678687022) * 10 ^ 70 +
        8051494605871567313071445052326139753917983563447960323203244455619373) * 10 ^ 70 +
        0477827140101822191096004654923475943260661637328378754594639775353233) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_137 :
    recurrence5LeadingSquare.coeff 137 =
      -((((55986758871640287973985593491015254385395844 * 10 ^ 70 +
        2429239121144579988776319408076955341496691636915017713435916275794214) * 10 ^ 70 +
        0563340805274718385429890275540143398410492379670391176459501665246360) * 10 ^ 70 +
        6767776004846578651467845914677350492683343820302940372963341854363782) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_138 :
    recurrence5LeadingSquare.coeff 138 =
      ((((42309301207394749114526225466292865916892849 * 10 ^ 70 +
        0101621279959584846499808996071167271573156043011438950461413870244129) * 10 ^ 70 +
        7612124349662134454843324380932741587325466359882348370057818980080224) * 10 ^ 70 +
        7494140422973452506830098496047281908825704505507922976366980533026342) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_139 :
    recurrence5LeadingSquare.coeff 139 =
      -((((30997881964934048676657399555357055207678595 * 10 ^ 70 +
        8239826179847636561805966845068809821893824655947454644954368506551599) * 10 ^ 70 +
        7040867123490159071725597411840490853593486008573294944983969524407062) * 10 ^ 70 +
        4988589589924008452634241890900576119937879288857778426868883175126548) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_140 :
    recurrence5LeadingSquare.coeff 140 =
      ((((21981937796973889427095325194097530639211753 * 10 ^ 70 +
        9510737895223571344908245942987315637374955216255004094968480100855757) * 10 ^ 70 +
        5591006090591881983747356606829846200220412055044511352076969174598560) * 10 ^ 70 +
        0746579319505646915258902279667005582007324362515255007214987688511401) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_141 :
    recurrence5LeadingSquare.coeff 141 =
      -((((15053532347131435926860320606854433761880355 * 10 ^ 70 +
        0951396057828333688833810422675492863224556459099984697882729191307882) * 10 ^ 70 +
        5926073483369839671533880122591318741201444168888298697571115609221265) * 10 ^ 70 +
        1292071535157148852265635837159133901095292567049612004358642873457104) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_142 :
    recurrence5LeadingSquare.coeff 142 =
      ((((9922452112511361394064969939919745837724322 * 10 ^ 70 +
        7306249313504241096210465224571164366526989737201475678795112665945457) * 10 ^ 70 +
        1620176886880381533460699923491827894824655950159511200150705566157147) * 10 ^ 70 +
        5464938119936842862613003091140585797449888148689420948842663428446797) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_143 :
    recurrence5LeadingSquare.coeff 143 =
      -((((6264901188806242284326216059749335027655291 * 10 ^ 70 +
        3350548301839257568678009830764725575791777842272671978429440625634099) * 10 ^ 70 +
        0844619017470742288832445342004331887809004251517996101345455778115097) * 10 ^ 70 +
        6001487849348893764128165764213146197919648744072597542532220045898756) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_144 :
    recurrence5LeadingSquare.coeff 144 =
      ((((3761420114917036626777584184704034509450106 * 10 ^ 70 +
        9030332881629408941794513542877104134705039041970348397995744257983270) * 10 ^ 70 +
        7111238060878443179657594256125752257791408834831149128949909281246258) * 10 ^ 70 +
        4964501464103047362421754151927561707236778843077888609543639376096590) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_145 :
    recurrence5LeadingSquare.coeff 145 =
      -((((2122567813219978507314431464354260935725732 * 10 ^ 70 +
        3413664143074393093989838859611505704775486083277336260818915489622298) * 10 ^ 70 +
        2343606714743642396877058805017621232040360225284885019415947625839318) * 10 ^ 70 +
        7743030247940050343228520425225709028399872080995237600590010830443564) : ℚ) := by
  unfold recurrence5LeadingSquare
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

private theorem recurrence5LeadingSquare_coeff_146_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (146 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_146_suffix_zero :
    (∑ x ∈ Finset.range 1,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (146 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_146 :
    recurrence5LeadingSquare.coeff 146 =
      ((((1103144369398619933525397511230423169127795 * 10 ^ 70 +
        9956160280854195536878011474694707449414010463023940610863450221667810) * 10 ^ 70 +
        7705440554808905369357022038625173636374420653762615286166044708686674) * 10 ^ 70 +
        8895455768574452082622402531362085926188445691891726031821819279749295) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 147 = 1 +
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
    rw [show 18 = 17 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_146_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_146_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_147_prefix_zero :
    (∑ x ∈ Finset.range 2,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (147 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (147 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_147_suffix_zero :
    (∑ x ∈ Finset.range 2,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (147 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_147 :
    recurrence5LeadingSquare.coeff 147 =
      -((((507096888130376186472648894450376749314160 * 10 ^ 70 +
        3395083354113912558006391155484098016453406664902858665526759887975145) * 10 ^ 70 +
        2753372328177790247853992483426907121101691636060468112950640939296032) * 10 ^ 70 +
        6824713142701729956427227272489923407095304048060195519926984517263312) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 148 = 2 +
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
    rw [show 18 = 16 +
      2 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_147_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_147_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_148_prefix_zero :
    (∑ x ∈ Finset.range 3,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (148 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (148 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_148_suffix_zero :
    (∑ x ∈ Finset.range 3,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (148 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_148 :
    recurrence5LeadingSquare.coeff 148 =
      ((((185792457761665591250443886146675305651750 * 10 ^ 70 +
        8618332169105016798746462321291580837832229245592361254357091502762711) * 10 ^ 70 +
        0474090707279551113410846110194603747309073082949948039834006466245012) * 10 ^ 70 +
        1254304630593849434664299979804870875689489489593418647573966245195460) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 149 = 3 +
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
    rw [show 18 = 15 +
      3 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_148_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_148_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_149_prefix_zero :
    (∑ x ∈ Finset.range 4,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (149 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (149 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_149_suffix_zero :
    (∑ x ∈ Finset.range 4,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (149 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_149 :
    recurrence5LeadingSquare.coeff 149 =
      -((((32263812902917402340912468344450399102860 * 10 ^ 70 +
        4234399182417490502956560691486885277625761598651009517386910114690764) * 10 ^ 70 +
        6909764155741976059666681405797412516304855172088414341011818964508437) * 10 ^ 70 +
        1655878883902033984481264719631892750549640606981189431842897391379520) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 150 = 4 +
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
    rw [show 18 = 14 +
      4 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_149_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_149_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_150_prefix_zero :
    (∑ x ∈ Finset.range 5,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (150 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (150 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_150_suffix_zero :
    (∑ x ∈ Finset.range 5,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (150 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_150 :
    recurrence5LeadingSquare.coeff 150 =
      -((((26414282384498192251138504142062701182595 * 10 ^ 70 +
        9535729430341391413863857752384152444020798755394890714578939715884225) * 10 ^ 70 +
        2120609717889678342196324157731070274602605973343865790643654288086536) * 10 ^ 70 +
        1890663757485069017482358957924363661281645706464889378212290519359155) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 151 = 5 +
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
    rw [show 18 = 13 +
      5 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_150_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_150_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_151_prefix_zero :
    (∑ x ∈ Finset.range 6,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (151 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (151 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_151_suffix_zero :
    (∑ x ∈ Finset.range 6,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (151 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_151 :
    recurrence5LeadingSquare.coeff 151 =
      ((((37052426003333889416293611867356182891226 * 10 ^ 70 +
        7697909268118925606142838482208925683958096113199184767901654141207600) * 10 ^ 70 +
        5402791024502216258427456115974459648285688409835608474004711553088722) * 10 ^ 70 +
        2515133273350348577944374482720375490885689459809515013861751397177984) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 152 = 6 +
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
    rw [show 18 = 12 +
      6 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_151_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_151_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_152_prefix_zero :
    (∑ x ∈ Finset.range 7,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (152 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (152 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_152_suffix_zero :
    (∑ x ∈ Finset.range 7,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (152 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_152 :
    recurrence5LeadingSquare.coeff 152 =
      -((((27591042294336266798017982824834856359882 * 10 ^ 70 +
        0147151944899741535648400062861038517692718324178825825926804249429951) * 10 ^ 70 +
        3004835516927124906629991813266598361988637317615239423375025686617615) * 10 ^ 70 +
        4949946012514417841237858219864141256025821431810263714384306639556064) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 153 = 7 +
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
    rw [show 18 = 11 +
      7 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_152_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_152_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_153_prefix_zero :
    (∑ x ∈ Finset.range 8,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (153 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (153 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_153_suffix_zero :
    (∑ x ∈ Finset.range 8,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (153 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_153 :
    recurrence5LeadingSquare.coeff 153 =
      ((((13153206931570719592663862059260795466841 * 10 ^ 70 +
        2462402709099151483918093780921885087321968484013605838385738024044235) * 10 ^ 70 +
        3914593298741410758816393166590578169971788107144156934679979775144133) * 10 ^ 70 +
        8494142587837344017080764363380153528933934024521168083520964738223778) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 154 = 8 +
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
    rw [show 18 = 10 +
      8 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_153_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_153_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_154_prefix_zero :
    (∑ x ∈ Finset.range 9,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (154 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (154 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_154_suffix_zero :
    (∑ x ∈ Finset.range 9,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (154 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_154 :
    recurrence5LeadingSquare.coeff 154 =
      -((((744643345152276387811968634684404506317 * 10 ^ 70 +
        7571611734216853639206587369078457895630682691497372617700524014930200) * 10 ^ 70 +
        4587536951537413428345249310084125807420837886400370667540516373764787) * 10 ^ 70 +
        9405619738679565040399531318272512397743468357137536509111343168875087) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 155 = 9 +
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
    rw [show 18 = 9 +
      9 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_154_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_154_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_155_prefix_zero :
    (∑ x ∈ Finset.range 10,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (155 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (155 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_155_suffix_zero :
    (∑ x ∈ Finset.range 10,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (155 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_155 :
    recurrence5LeadingSquare.coeff 155 =
      -((((7336739104398618569439480662683547387135 * 10 ^ 70 +
        7110016722873097953764797406804327056795760121388080574771242957799447) * 10 ^ 70 +
        9286377599716706569291600309453947954918140162700648402107895963577935) * 10 ^ 70 +
        0112629252865083335012828461117872979727330771584781615342144200051554) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 156 = 10 +
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
    rw [show 18 = 8 +
      10 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_155_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_155_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_156_prefix_zero :
    (∑ x ∈ Finset.range 11,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (156 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (156 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_156_suffix_zero :
    (∑ x ∈ Finset.range 11,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (156 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_156 :
    recurrence5LeadingSquare.coeff 156 =
      ((((11196388882370625535179499330092978495252 * 10 ^ 70 +
        2781570704897720685441144224790637233867038047933609253428000868868002) * 10 ^ 70 +
        7001530783834971526887044053651486048323362101841494445671526964666099) * 10 ^ 70 +
        0777876047426249867533758775995269197509432824762989643017017482276455) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 157 = 11 +
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
    rw [show 18 = 7 +
      11 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_156_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_156_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_157_prefix_zero :
    (∑ x ∈ Finset.range 12,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (157 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (157 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_157_suffix_zero :
    (∑ x ∈ Finset.range 12,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (157 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_157 :
    recurrence5LeadingSquare.coeff 157 =
      -((((11908587128675596295027181324487037892638 * 10 ^ 70 +
        0959795552857866653483379738766458558053220988130852734815415881706191) * 10 ^ 70 +
        9885212434275054061503584503358195070271426750672183685759173906257499) * 10 ^ 70 +
        4882063331552636807532209198849962111327681752569137292395945026573166) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 158 = 12 +
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
    rw [show 18 = 6 +
      12 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_157_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_157_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_158_prefix_zero :
    (∑ x ∈ Finset.range 13,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (158 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (158 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_158_suffix_zero :
    (∑ x ∈ Finset.range 13,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (158 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_158 :
    recurrence5LeadingSquare.coeff 158 =
      ((((10715547922557629161707611747738648215031 * 10 ^ 70 +
        0773583484781037681528613973877169942805832550674416553716984953597943) * 10 ^ 70 +
        9535832487872205554638593953946638808474672092181678688078288495722095) * 10 ^ 70 +
        7487966323029723598087465036211429232178307876218512332033091028636702) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 159 = 13 +
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
    rw [show 18 = 5 +
      13 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_158_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_158_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5LeadingSquare_coeff_159_prefix_zero :
    (∑ x ∈ Finset.range 14,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (159 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (159 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_159_suffix_zero :
    (∑ x ∈ Finset.range 14,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (159 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_159 :
    recurrence5LeadingSquare.coeff 159 =
      -((((8651571969695396303885732432255766503670 * 10 ^ 70 +
        2645572467563829294780877692347509200748357996456706847619836796006494) * 10 ^ 70 +
        9248424293740024258677375736472943325502740662983207538831582555566115) * 10 ^ 70 +
        7015624977682508465095547413606660564939373462659206435011993211146334) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 160 = 14 +
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
    rw [show 18 = 4 +
      14 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_159_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_159_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
