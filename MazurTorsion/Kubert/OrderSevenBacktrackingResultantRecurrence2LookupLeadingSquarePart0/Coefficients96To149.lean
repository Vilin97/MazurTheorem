/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB5
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupLeadingSquarePart0Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: LeadingSquare coefficient convolution

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence2B5_coeff_0
  recurrence2B5_coeff_1
  recurrence2B5_coeff_2
  recurrence2B5_coeff_3
  recurrence2B5_coeff_4
  recurrence2B5_coeff_5
  recurrence2B5_coeff_6
  recurrence2B5_coeff_7
  recurrence2B5_coeff_8
  recurrence2B5_coeff_9
  recurrence2B5_coeff_10
  recurrence2B5_coeff_11
  recurrence2B5_coeff_12
  recurrence2B5_coeff_13
  recurrence2B5_coeff_14
  recurrence2B5_coeff_15
  recurrence2B5_coeff_16
  recurrence2B5_coeff_17
  recurrence2B5_coeff_18
  recurrence2B5_coeff_19
  recurrence2B5_coeff_20
  recurrence2B5_coeff_21
  recurrence2B5_coeff_22
  recurrence2B5_coeff_23
  recurrence2B5_coeff_24
  recurrence2B5_coeff_25
  recurrence2B5_coeff_26
  recurrence2B5_coeff_27
  recurrence2B5_coeff_28
  recurrence2B5_coeff_29
  recurrence2B5_coeff_30
  recurrence2B5_coeff_31
  recurrence2B5_coeff_32
  recurrence2B5_coeff_33
  recurrence2B5_coeff_34
  recurrence2B5_coeff_35
  recurrence2B5_coeff_36
  recurrence2B5_coeff_37
  recurrence2B5_coeff_38
  recurrence2B5_coeff_39
  recurrence2B5_coeff_40
  recurrence2B5_coeff_41
  recurrence2B5_coeff_42
  recurrence2B5_coeff_43
  recurrence2B5_coeff_44
  recurrence2B5_coeff_45
  recurrence2B5_coeff_46
  recurrence2B5_coeff_47
  recurrence2B5_coeff_48
  recurrence2B5_coeff_49
  recurrence2B5_coeff_50
  recurrence2B5_coeff_51
  recurrence2B5_coeff_52
  recurrence2B5_coeff_53
  recurrence2B5_coeff_54
  recurrence2B5_coeff_55
  recurrence2B5_coeff_56
  recurrence2B5_coeff_57
  recurrence2B5_coeff_58
  recurrence2B5_coeff_59
  recurrence2B5_coeff_60
  recurrence2B5_coeff_61
  recurrence2B5_coeff_62
  recurrence2B5_coeff_63
  recurrence2B5_coeff_64
  recurrence2B5_coeff_65
  recurrence2B5_coeff_66
  recurrence2B5_coeff_67
  recurrence2B5_coeff_68
  recurrence2B5_coeff_69
  recurrence2B5_coeff_70
  recurrence2B5_coeff_71
  recurrence2B5_coeff_72
  recurrence2B5_coeff_73
  recurrence2B5_coeff_74
  recurrence2B5_coeff_75
  recurrence2B5_coeff_76
  recurrence2B5_coeff_77
  recurrence2B5_coeff_78
  recurrence2B5_coeff_79
  recurrence2B5_coeff_80
  recurrence2B5_coeff_81
  recurrence2B5_coeff_82
  recurrence2B5_coeff_83
  recurrence2B5_coeff_84
  recurrence2B5_coeff_85
  recurrence2B5_coeff_86
  recurrence2B5_coeff_87
  recurrence2B5_coeff_88
  recurrence2B5_coeff_89
  recurrence2B5_coeff_90
  recurrence2B5_coeff_91
  recurrence2B5_coeff_92
  recurrence2B5_coeff_93
  recurrence2B5_coeff_94
  recurrence2B5_coeff_95
  recurrence2B5_coeff_96
  recurrence2B5_coeff_97
  recurrence2B5_coeff_98
  recurrence2B5_coeff_99
  recurrence2B5_coeff_100
  recurrence2B5_coeff_101
  recurrence2B5_coeff_102
  recurrence2B5_coeff_103
  recurrence2B5_coeff_104
  recurrence2B5_coeff_105
  recurrence2B5_coeff_106
  recurrence2B5_coeff_107
  recurrence2B5_coeff_108
  recurrence2B5_coeff_109
  recurrence2B5_coeff_110
  recurrence2B5_coeff_111
  recurrence2B5_coeff_112
  recurrence2B5_coeff_113
  recurrence2B5_coeff_114
  recurrence2B5_coeff_115
  recurrence2B5_coeff_116
  recurrence2B5_coeff_117
  recurrence2B5_coeff_118
  recurrence2B5_coeff_119
  recurrence2B5_coeff_120
  recurrence2B5_coeff_121
  recurrence2B5_coeff_122
  recurrence2B5_coeff_123
  recurrence2B5_coeff_124
  recurrence2B5_coeff_125
  recurrence2B5_coeff_126
  recurrence2B5_coeff_127
  recurrence2B5_coeff_128
  recurrence2B5_coeff_129
  recurrence2B5_coeff_130
  recurrence2B5_coeff_131
  recurrence2B5_coeff_132
  recurrence2B5_coeff_133
  recurrence2B5_coeff_134

theorem recurrence2LeadingSquare_coeff_96 :
    recurrence2LeadingSquare.coeff 96 =
      ((157846186778598447908164418970692465306467415584558434727 * 10 ^ 70 +
        8128447157884899476689042547928480677143660965109184228561630879825972) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2LeadingSquare_coeff_97 :
    recurrence2LeadingSquare.coeff 97 =
      -((1670429066990176734232327998742154398578612149133627457689 * 10 ^ 70 +
        3720401662922000921343488847023861156470370919124917429576305220827090) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2LeadingSquare_coeff_98 :
    recurrence2LeadingSquare.coeff 98 =
      ((7725143053335460835965367296797683514233644579300017387671 * 10 ^ 70 +
        5067911669526184849763609866155337930041890431314384270076861332236055) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2LeadingSquare_coeff_99 :
    recurrence2LeadingSquare.coeff 99 =
      -((20603394452310131154964617401398347196975129439636699403343 * 10 ^ 70 +
        1785996162018714235616266223468497153518629961363489912641374411728908) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2LeadingSquare_coeff_100 :
    recurrence2LeadingSquare.coeff 100 =
      ((15261406093131292905059057272689885263933029884955280910443 * 10 ^ 70 +
        1342865675694480756557780616720085523959343634311884784694203106923463) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2LeadingSquare_coeff_101 :
    recurrence2LeadingSquare.coeff 101 =
      ((163356324785470515027778279245006027767206694934607601267964 * 10 ^ 70 +
        3113176368620682901699138952626392676860522829638632025940592993443346) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2LeadingSquare_coeff_102 :
    recurrence2LeadingSquare.coeff 102 =
      -((1102326691753237734382163760530621342138217551764984257815714 * 10 ^ 70 +
        9727736450256423514491544259336255439251458689412594182561213377916927) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2LeadingSquare_coeff_103 :
    recurrence2LeadingSquare.coeff 103 =
      ((4584396483976878663569583194660126858025253455187353860826006 * 10 ^ 70 +
        0475075755888784775599454846323587853086065878876688810808467747032230) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2LeadingSquare_coeff_104 :
    recurrence2LeadingSquare.coeff 104 =
      -((14548421100598952294859432809750726934168811060316681742443453 * 10 ^ 70 +
        6097275216637973005367129975542385059472830216365693168472744855537050) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2LeadingSquare_coeff_105 :
    recurrence2LeadingSquare.coeff 105 =
      ((29373365727822772651315534907765947170908203867612735218605949 * 10 ^ 70 +
        9441111297606913566222959716387382354545305151612205724482111473981622) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2LeadingSquare_coeff_106 :
    recurrence2LeadingSquare.coeff 106 =
      ((33119853375609169307101594881972325381718010916073502782035683 * 10 ^ 70 +
        9981087170846709784090457454395853809781705476415923588685033252816250) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2LeadingSquare_coeff_107 :
    recurrence2LeadingSquare.coeff 107 =
      -((685284804867397969506277035574958163410462114861229669519407748 * 10 ^ 70 +
        7365007408015039121316552526604154693879845086650303244501712971096492) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2LeadingSquare_coeff_108 :
    recurrence2LeadingSquare.coeff 108 =
      ((3743093430141601083750949604430527541968293612345933606710459077 * 10 ^ 70 +
        7436505697414459669084226242535476828966221810251772086745659793612198) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2LeadingSquare_coeff_109 :
    recurrence2LeadingSquare.coeff 109 =
      -((12124058065726019354730138251233727366761802976115680870295572758 * 10 ^ 70 +
        8474091074526797743126596296322445472795872083649834876789133535575094) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2LeadingSquare_coeff_110 :
    recurrence2LeadingSquare.coeff 110 =
      ((17773536928767036460537532885963490567387372039480937327616296707 * 10 ^ 70 +
        6334235737908574609538108804047837503005640652103287609141659319344273) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2LeadingSquare_coeff_111 :
    recurrence2LeadingSquare.coeff 111 =
      ((52073771648209923075933990668844144266680550152265407245473791750 * 10 ^ 70 +
        4248707029660271032073164635585126160435931742792672014487583794933366) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2LeadingSquare_coeff_112 :
    recurrence2LeadingSquare.coeff 112 =
      -((439295910728159856955971496979837235606592925397556078319432121881 * 10 ^ 70 +
        7576975876066425738256229728570143708173586108439006319863296316067675) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2LeadingSquare_coeff_113 :
    recurrence2LeadingSquare.coeff 113 =
      ((1446903836750173139053468137495081414387795592654926675287977725060 * 10 ^ 70 +
        9537264637972036066516306319811442755068509019853484140107614297089066) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2LeadingSquare_coeff_114 :
    recurrence2LeadingSquare.coeff 114 =
      -((2092866325862145812716324095455641809639770088505334894415880428798 * 10 ^ 70 +
        5755248581907852012935952901814775196365298190982278649910928645277364) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2LeadingSquare_coeff_115 :
    recurrence2LeadingSquare.coeff 115 =
      -((3307688722500730860915948909298574561245873549985076619759800432378 * 10 ^ 70 +
        4648429580238387640212392773461591125625320554605934272649794462494998) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2LeadingSquare_coeff_116 :
    recurrence2LeadingSquare.coeff 116 =
      ((22218468420369964324535673889224781727985507726600152421943770600965 * 10 ^ 70 +
        3977230501862702121561585632753289185806369088348618888042812324162710) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2LeadingSquare_coeff_117 :
    recurrence2LeadingSquare.coeff 117 =
      -((13055671636421636162079515526591490776496110134790595129118555889178 * 10 ^ 70 +
        9598392539234822003856857388930033038409510835697549023939940428901924) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2LeadingSquare_coeff_118 :
    recurrence2LeadingSquare.coeff 118 =
      -((279779800014477396606459215756382846142641694873276805329868884778647 * 10 ^ 70 +
        8029528746635877991564320465931982263080230458347220807711243653454049) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2LeadingSquare_coeff_119 :
    recurrence2LeadingSquare.coeff 119 =
      ((1393319114033394439029819835769816224318705326995900886869257427694368 * 10 ^ 70 +
        8912501832527321760409916153879472697233542915138858094130767003822902) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2LeadingSquare_coeff_120 :
    recurrence2LeadingSquare.coeff 120 =
      -((2472438213610324242786198977464171957645031803439339978851413313679951 * 10 ^ 70 +
        2070755573060900821317347820743577414159782899862321451211016063898669) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2LeadingSquare_coeff_121 :
    recurrence2LeadingSquare.coeff 121 =
      -((6814088707675147899554930422067721085540997021707608564447334461376861 * 10 ^ 70 +
        5944475427116201893611318460546207823563924769082237679730582020349292) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2LeadingSquare_coeff_122 :
    recurrence2LeadingSquare.coeff 122 =
      (((6 * 10 ^ 70 +
        3423570036753966360206743459199024000555822784112802400939567385026733) * 10 ^ 70 +
        0155210296633810079538353155240110984683065164021086506850098254003094) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2LeadingSquare_coeff_123 :
    recurrence2LeadingSquare.coeff 123 =
      -(((22 * 10 ^ 70 +
        1960907548154617623545659641519969580531095315760597439535733178547826) * 10 ^ 70 +
        5366437919030372441789884648544813195800492198565141735401435334960000) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2LeadingSquare_coeff_124 :
    recurrence2LeadingSquare.coeff 124 =
      (((34 * 10 ^ 70 +
        9612944165184439303148036766982546315986163008374216009496531943587984) * 10 ^ 70 +
        6527635019298971556653511055679971263613145026873267892800930454289025) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2LeadingSquare_coeff_125 :
    recurrence2LeadingSquare.coeff 125 =
      (((63 * 10 ^ 70 +
        9719438783264085538409550553002109183745669353649001421797263542765112) * 10 ^ 70 +
        7682031645400903767994399767816405280865468604258427561526787346229610) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2LeadingSquare_coeff_126 :
    recurrence2LeadingSquare.coeff 126 =
      -(((604 * 10 ^ 70 +
        0615642135954055356341977900701838952077255321877669633645376833649151) * 10 ^ 70 +
        3619934009002787473999624522352534794405780449290125472679214555288911) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2LeadingSquare_coeff_127 :
    recurrence2LeadingSquare.coeff 127 =
      (((1952 * 10 ^ 70 +
        1707632110454729277662781600251795563947306926103907226282384685516579) * 10 ^ 70 +
        6889755074215391479558761148607299224829114762974382057757384830627120) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2LeadingSquare_coeff_128 :
    recurrence2LeadingSquare.coeff 128 =
      -(((2613 * 10 ^ 70 +
        3545369177609399455890395614331703802246369704296182880269184418655870) * 10 ^ 70 +
        7283359220335406268953379690545375239934159721778095995408245147581345) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2LeadingSquare_coeff_129 :
    recurrence2LeadingSquare.coeff 129 =
      -(((7091 * 10 ^ 70 +
        5691864577149768926810929255568430357691676325082267752345436059414901) * 10 ^ 70 +
        6336734843057492176949660243425412051882869500778933932767234410358566) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2LeadingSquare_coeff_130 :
    recurrence2LeadingSquare.coeff 130 =
      (((55117 * 10 ^ 70 +
        5694623889764030871145432116318841685712692433020241134280636991406442) * 10 ^ 70 +
        5791031783297270032539055078284053524254708730354145637430735054371585) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2LeadingSquare_coeff_131 :
    recurrence2LeadingSquare.coeff 131 =
      -(((176760 * 10 ^ 70 +
        4034590504280409570926728531885847408550061124162402356471873642544606) * 10 ^ 70 +
        3587716140110992780900711070724538028297719863833485704742388558025464) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2LeadingSquare_coeff_132 :
    recurrence2LeadingSquare.coeff 132 =
      (((286009 * 10 ^ 70 +
        2046735638879719840769902486434859493487410921943053844931752171039040) * 10 ^ 70 +
        9036110816913150421308376503012183185535325704814288243677816683952566) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2LeadingSquare_coeff_133 :
    recurrence2LeadingSquare.coeff 133 =
      (((275662 * 10 ^ 70 +
        6186128227347169050744280682499727262922021103926008786179405074967604) * 10 ^ 70 +
        2641114264806503043557665585755214944560262949271222465890255445310792) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2LeadingSquare_coeff_134 :
    recurrence2LeadingSquare.coeff 134 =
      -(((3623464 * 10 ^ 70 +
        5464072136910748223539869469800293570484387924943389890994291568748586) * 10 ^ 70 +
        4775821912114220047945951446925971448353991270267780694933629703020337) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

private theorem recurrence2LeadingSquare_coeff_135_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (135 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_135_suffix_zero :
    (∑ x ∈ Finset.range 1,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (135 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_135 :
    recurrence2LeadingSquare.coeff 135 =
      (((13590907 * 10 ^ 70 +
        4745195424752098118103703517193268842403414982506677004514271849854132) * 10 ^ 70 +
        1394167966908160736082283861410363808030843663674022193708770943967368) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 136 = 1 +
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
    rw [show 7 = 6 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_135_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_135_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2LeadingSquare_coeff_136_prefix_zero :
    (∑ x ∈ Finset.range 2,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (136 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (136 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_136_suffix_zero :
    (∑ x ∈ Finset.range 2,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (136 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_136 :
    recurrence2LeadingSquare.coeff 136 =
      -(((30245024 * 10 ^ 70 +
        0413615064541133901438792852709589264407368312482878403665295029387273) * 10 ^ 70 +
        6922024675802288246888690380443452949953909323938873267433903664257660) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 137 = 2 +
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
    rw [show 7 = 5 +
      2 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_136_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_136_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2LeadingSquare_coeff_137_prefix_zero :
    (∑ x ∈ Finset.range 3,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (137 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (137 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_137_suffix_zero :
    (∑ x ∈ Finset.range 3,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (137 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_137 :
    recurrence2LeadingSquare.coeff 137 =
      (((25007527 * 10 ^ 70 +
        7522352301898421103830143795787611488123060391563640800199516627574736) * 10 ^ 70 +
        5517742950918946852479265179109352711348131893297811516653471660136760) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 138 = 3 +
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
    rw [show 7 = 4 +
      3 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_137_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_137_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2LeadingSquare_coeff_138_prefix_zero :
    (∑ x ∈ Finset.range 4,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (138 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (138 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_138_suffix_zero :
    (∑ x ∈ Finset.range 4,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (138 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_138 :
    recurrence2LeadingSquare.coeff 138 =
      (((124750169 * 10 ^ 70 +
        7215321067478409163691452154640468245967876360716674413920597722133017) * 10 ^ 70 +
        5010518363274600465709541149849203777141078740249228458145811924408812) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 139 = 4 +
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
    rw [show 7 = 3 +
      4 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_138_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_138_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2LeadingSquare_coeff_139_prefix_zero :
    (∑ x ∈ Finset.range 5,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (139 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (139 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_139_suffix_zero :
    (∑ x ∈ Finset.range 5,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (139 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_139 :
    recurrence2LeadingSquare.coeff 139 =
      -(((738017727 * 10 ^ 70 +
        3947936090539073303376616748107206482061787932786178395077098356391322) * 10 ^ 70 +
        4216401372827148516844860012725962057969097247387769875756914183025586) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 140 = 5 +
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
    rw [show 7 = 2 +
      5 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_139_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_139_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2LeadingSquare_coeff_140_prefix_zero :
    (∑ x ∈ Finset.range 6,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (140 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (140 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_140_suffix_zero :
    (∑ x ∈ Finset.range 6,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (140 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_140 :
    recurrence2LeadingSquare.coeff 140 =
      (((2318862789 * 10 ^ 70 +
        4228720405061066879614481958599753494807435633363267687624221435887136) * 10 ^ 70 +
        5778944569515939199929900980244875778131912911605879265443678989941987) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 141 = 6 +
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
    rw [show 7 = 1 +
      6 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_140_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_140_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2LeadingSquare_coeff_141_prefix_zero :
    (∑ x ∈ Finset.range 7,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (141 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (141 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_141_suffix_zero :
    (∑ x ∈ Finset.range 7,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (141 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_141 :
    recurrence2LeadingSquare.coeff 141 =
      -(((4839192002 * 10 ^ 70 +
        1062759374922098142608987701986882614892218945552616525120573862564905) * 10 ^ 70 +
        5519709293228537002744909432556539322558955854168562518293379414331722) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 142 = 7 +
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
  rw [recurrence2LeadingSquare_coeff_141_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_141_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2LeadingSquare_coeff_142_prefix_zero :
    (∑ x ∈ Finset.range 8,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (142 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (142 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_142_suffix_zero :
    (∑ x ∈ Finset.range 8,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (142 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_142 :
    recurrence2LeadingSquare.coeff 142 =
      (((4809602106 * 10 ^ 70 +
        1338661827595414025462406821169814448229667671925164321375052813598835) * 10 ^ 70 +
        8212034820825667458635825776729392236312840385836440742362631072457931) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 143 = 8 +
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
    rw [show 39 = 31 +
      8 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_142_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_142_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2LeadingSquare_coeff_143_prefix_zero :
    (∑ x ∈ Finset.range 9,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (143 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (143 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_143_suffix_zero :
    (∑ x ∈ Finset.range 9,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (143 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_143 :
    recurrence2LeadingSquare.coeff 143 =
      (((12519173615 * 10 ^ 70 +
        4695317005208545369364065390327730318625002707922312563168684742511286) * 10 ^ 70 +
        8140394040176269186718330663406016538496013852635235241721014444096802) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 144 = 9 +
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
    rw [show 39 = 30 +
      9 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_143_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_143_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2LeadingSquare_coeff_144_prefix_zero :
    (∑ x ∈ Finset.range 10,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (144 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (144 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_144_suffix_zero :
    (∑ x ∈ Finset.range 10,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (144 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_144 :
    recurrence2LeadingSquare.coeff 144 =
      -(((88066892556 * 10 ^ 70 +
        7552921090909069505610040974415789009715718740905405632945626882074022) * 10 ^ 70 +
        5330248499955107861215400167035476019069401150292329679010738810568846) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 145 = 10 +
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
    rw [show 39 = 29 +
      10 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_144_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_144_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2LeadingSquare_coeff_145_prefix_zero :
    (∑ x ∈ Finset.range 11,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (145 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (145 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_145_suffix_zero :
    (∑ x ∈ Finset.range 11,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (145 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_145 :
    recurrence2LeadingSquare.coeff 145 =
      (((305432375529 * 10 ^ 70 +
        4087940249589223722023879402786940708439660669362923102388038121118301) * 10 ^ 70 +
        9890232713257129213073023894348858517586720482446642819095092562375940) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 146 = 11 +
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
    rw [show 39 = 28 +
      11 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_145_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_145_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2LeadingSquare_coeff_146_prefix_zero :
    (∑ x ∈ Finset.range 12,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (146 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (146 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_146_suffix_zero :
    (∑ x ∈ Finset.range 12,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (146 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_146 :
    recurrence2LeadingSquare.coeff 146 =
      -(((774808611791 * 10 ^ 70 +
        1400061978681725633010584534741957188038533809761026786215722729856771) * 10 ^ 70 +
        6644980729176630721819064282424621461093659529089084128927557856591460) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 147 = 12 +
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
    rw [show 39 = 27 +
      12 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_146_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_146_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2LeadingSquare_coeff_147_prefix_zero :
    (∑ x ∈ Finset.range 13,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (147 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (147 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_147_suffix_zero :
    (∑ x ∈ Finset.range 13,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (147 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_147 :
    recurrence2LeadingSquare.coeff 147 =
      (((1474787002410 * 10 ^ 70 +
        6372141496634960211141421921448609751302027119427342315804677288664001) * 10 ^ 70 +
        8260390615905870445831248501843141642749154276027059874903362776491762) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 148 = 13 +
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
    rw [show 39 = 26 +
      13 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_147_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_147_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2LeadingSquare_coeff_148_prefix_zero :
    (∑ x ∈ Finset.range 14,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (148 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (148 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_148_suffix_zero :
    (∑ x ∈ Finset.range 14,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (148 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_148 :
    recurrence2LeadingSquare.coeff 148 =
      -(((1680899995858 * 10 ^ 70 +
        1183219590352725847962921900759382545374071679525590875062757812356931) * 10 ^ 70 +
        5663146268865874482641583156592039313815314546398006877840262174624803) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 149 = 14 +
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
    rw [show 39 = 25 +
      14 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_148_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_148_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2LeadingSquare_coeff_149_prefix_zero :
    (∑ x ∈ Finset.range 15,
      remainder3Coefficient5.coeff x * remainder3Coefficient5.coeff (149 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (149 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2LeadingSquare_coeff_149_suffix_zero :
    (∑ x ∈ Finset.range 15,
      remainder3Coefficient5.coeff (135 + x) *
        remainder3Coefficient5.coeff (149 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5_coeff_high (135 + x) (by omega)]
  norm_num

theorem recurrence2LeadingSquare_coeff_149 :
    recurrence2LeadingSquare.coeff 149 =
      -(((1585107786913 * 10 ^ 70 +
        5550653012737987363500830326285951538596939471403320568102016159033243) * 10 ^ 70 +
        3148812983325335498117729879801095408148339201654025793702354158501974) : ℚ) := by
  unfold recurrence2LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 150 = 15 +
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
    rw [show 39 = 24 +
      15 by norm_num, Finset.sum_range_add]
  rw [recurrence2LeadingSquare_coeff_149_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2LeadingSquare_coeff_149_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
