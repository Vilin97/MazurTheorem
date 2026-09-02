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

theorem recurrence5LeadingSquare_coeff_0 :
    recurrence5LeadingSquare.coeff 0 =
      ((11833853149689105471167568027241384 * 10 ^ 70 +
        0553898670382393757294020088346407726692763844052057745054317870780416) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_1 :
    recurrence5LeadingSquare.coeff 1 =
      ((18657548722128585913479566940949447136 * 10 ^ 70 +
        3290491191641557593684421789155082096978795628575542296263913019173376) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_2 :
    recurrence5LeadingSquare.coeff 2 =
      ((235101870311298220221378239005051419472686 * 10 ^ 70 +
        8556886278326972172745980090757040843501767968185901468251817605327504) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_3 :
    recurrence5LeadingSquare.coeff 3 =
      -((172843817402393847946708412420423799357874656 * 10 ^ 70 +
        2021168537143160147428405166637682661372572065171522953655482848607264) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_4 :
    recurrence5LeadingSquare.coeff 4 =
      ((1149203722405858028148555409972046782305477595698 * 10 ^ 70 +
        9292699100281151389011689938632158301962879533530120434798118997395632) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_5 :
    recurrence5LeadingSquare.coeff 5 =
      -((3270322525860258061579608290852272131960085799433868 * 10 ^ 70 +
        4521932528035011508558992410070044129160463608497541261508085806621184) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_6 :
    recurrence5LeadingSquare.coeff 6 =
      ((5690933538731394156328841454763539735746932241237497279 * 10 ^ 70 +
        0137477442217143867384001223121939660333187462171092441805973111482000) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_7 :
    recurrence5LeadingSquare.coeff 7 =
      -((6250009434405067378800653876282974952987209137002913287688 * 10 ^ 70 +
        3873764689468930500246927905185327525125583258808010517708668005597024) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_8 :
    recurrence5LeadingSquare.coeff 8 =
      ((4335872470996574436153572996408442247995157986414918884264131 * 10 ^ 70 +
        9078866117649644800832206721070930221975551846314514746662707788263616) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_9 :
    recurrence5LeadingSquare.coeff 9 =
      -((1457171923895690652893704361153228866086735429408709127059051679 * 10 ^ 70 +
        2083802778703232309275031536946213715910180480353003430876954020543648) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_10 :
    recurrence5LeadingSquare.coeff 10 =
      -((528690301657783318681075211850669112636755199911244659627593795031 * 10 ^ 70 +
        0536040667294975622664927517660055030683021478330850917029541823406816) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_11 :
    recurrence5LeadingSquare.coeff 11 =
      ((1040214272215712578652297545901559602241126090683774375254495402973947 * 10 ^ 70 +
        0562309453856724739399443700990763928211983997557133931883275350586792) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_12 :
    recurrence5LeadingSquare.coeff 12 =
      -(((69 * 10 ^ 70 +
        7991734077248133102867945792956058373352298424486818145520941219170854) * 10 ^ 70 +
        4005532981105596422521971723376461390463806011013706773637726395802248) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_13 :
    recurrence5LeadingSquare.coeff 13 =
      (((26183 * 10 ^ 70 +
        9895102001167918341368009494695113586193123717342230960895845501754779) * 10 ^ 70 +
        0842606283968741529935845282288086370265896945212503976768571029783560) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_14 :
    recurrence5LeadingSquare.coeff 14 =
      -(((3324662 * 10 ^ 70 +
        0575251164469359314339312647035439846770578036115519919944820046567161) * 10 ^ 70 +
        1864868289354914725324276655568617314525606495747798038295718470016484) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_15 :
    recurrence5LeadingSquare.coeff 15 =
      -(((2683417744 * 10 ^ 70 +
        2060495642337081644165246260349647298312397787070453061746475931162450) * 10 ^ 70 +
        6857682167469052233829931196259533568846540871117846128470172022351744) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_16 :
    recurrence5LeadingSquare.coeff 16 =
      (((2284521094244 * 10 ^ 70 +
        8676047809722087357367337397714567321987144967489860887878229041638183) * 10 ^ 70 +
        9422443647073224374264880827233590047233111851218329406350075367402068) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_17 :
    recurrence5LeadingSquare.coeff 17 =
      -(((1053335018931406 * 10 ^ 70 +
        7516563989975260259090928814033631677463913682674715192733591765279928) * 10 ^ 70 +
        7627538797225282138315162275833616487058889956550871818663626553256516) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_18 :
    recurrence5LeadingSquare.coeff 18 =
      (((358612844244235408 * 10 ^ 70 +
        3932628176031424877984945055955219087134096398704532952612159812071232) * 10 ^ 70 +
        2254235292219811332992559083034319896485604774613077173323351598862448) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_19 :
    recurrence5LeadingSquare.coeff 19 =
      -(((98164931782345975941 * 10 ^ 70 +
        7735137412012589230896894917533435620966311918084260028854094542613532) * 10 ^ 70 +
        9247229317176694323906163156487627339154946864511948351992087788286924) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_20 :
    recurrence5LeadingSquare.coeff 20 =
      (((22463814132732250144553 * 10 ^ 70 +
        5759329796293583932210509468150419438746352489295693958378041498644451) * 10 ^ 70 +
        7884511234606769197911960096485809657214534959550780061243317116955801) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_21 :
    recurrence5LeadingSquare.coeff 21 =
      -(((4395472978015941807736660 * 10 ^ 70 +
        3704624668889185586180690920483493072398697726973484799749470241408573) * 10 ^ 70 +
        1771804030803362041807255067299327168044415662962560957668297921807084) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_22 :
    recurrence5LeadingSquare.coeff 22 =
      (((746506793732199922982938463 * 10 ^ 70 +
        7715340422317358367981644820614953844408406813385208016752472049588998) * 10 ^ 70 +
        3988783564995329313811199686375781930135327543198811864112314449060264) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_23 :
    recurrence5LeadingSquare.coeff 23 =
      -(((111250334132399326889030781724 * 10 ^ 70 +
        5974318069011369181650494688997575415086696025595604326927777209412628) * 10 ^ 70 +
        0178245491026222559738777367649518700059535756280496862100681291142904) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_24 :
    recurrence5LeadingSquare.coeff 24 =
      (((14671380777600920148372232471024 * 10 ^ 70 +
        1568382432464288265209590429205870430465630024108649499945089424231225) * 10 ^ 70 +
        1688923267034447214250448432185903266519579554645227370913387577282664) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_25 :
    recurrence5LeadingSquare.coeff 25 =
      -(((1723884205127214082105491511487179 * 10 ^ 70 +
        8915775174418413413101452625229353186270674606230299921637687444874354) * 10 ^ 70 +
        5071550943426567297930368117885145895856489423597903621841655659199084) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_26 :
    recurrence5LeadingSquare.coeff 26 =
      (((181507932478911942080100555769493463 * 10 ^ 70 +
        7695039370257206558722288482840897841004874299721485927816920121143523) * 10 ^ 70 +
        5095491014835606801696034937843042573767012580881171216663315351063152) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_27 :
    recurrence5LeadingSquare.coeff 27 =
      -(((17209426230754950879417145887645105428 * 10 ^ 70 +
        9681588572061536471167368496013081326865515658453230788836910688166771) * 10 ^ 70 +
        3532559264785612306625360669198120492113532341673107968341775899829234) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_28 :
    recurrence5LeadingSquare.coeff 28 =
      (((1475668308952899105833920776229318337194 * 10 ^ 70 +
        8765176891622595345434335672817013737532030094918491154421619698889856) * 10 ^ 70 +
        4505775367834762626417635575815958059884075057979212359627708292429232) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_29 :
    recurrence5LeadingSquare.coeff 29 =
      -(((114874685981951686426385737033340773581683 * 10 ^ 70 +
        1935955363969670196976513341378131759474346346146041382576961602230537) * 10 ^ 70 +
        8636744198559939795785938113436208912189507901364475142963423240141176) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_30 :
    recurrence5LeadingSquare.coeff 30 =
      (((8146456101539454240008640012154459380238812 * 10 ^ 70 +
        9380331262565138158287791255718592465074773280848395538668433277456573) * 10 ^ 70 +
        4539269231295405394407838231965691077968935662234044452240597345416812) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_31 :
    recurrence5LeadingSquare.coeff 31 =
      -(((527935466421205317820764793186023826942023048 * 10 ^ 70 +
        3554556767612298201045823433781251930448095406482011610328881864744178) * 10 ^ 70 +
        1351258682281477729684339064525131004529596133380890446225251108664720) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_32 :
    recurrence5LeadingSquare.coeff 32 =
      (((31354869684151182846194986475980964936400816417 * 10 ^ 70 +
        6722703792654210133511120213103230209079829308439006821038077319156433) * 10 ^ 70 +
        1559874486984564870929528598648530894216104234762376220137141153323076) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_33 :
    recurrence5LeadingSquare.coeff 33 =
      -(((1711148918497436488372444657296152548825143136681 * 10 ^ 70 +
        3296467164048994930845621912524195018424006613077054479281008083135799) * 10 ^ 70 +
        5532860499553147230961493923052356497694211533646686777695399485670122) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_34 :
    recurrence5LeadingSquare.coeff 34 =
      (((86018420364287819282068377427637111554285978547649 * 10 ^ 70 +
        0095218428589053821909711144595796363317506540711197066977190164776757) * 10 ^ 70 +
        1568698233707777180010935092732531428901557647596397943373548754805129) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_35 :
    recurrence5LeadingSquare.coeff 35 =
      -(((3992128163904872113444933610499971376595121721944940 * 10 ^ 70 +
        1157793138855923520373005841231698159657483714423887899213940691521488) * 10 ^ 70 +
        1752123307383922460555451575116386532933798654001131048019415891208420) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_36 :
    recurrence5LeadingSquare.coeff 36 =
      (((171415629873020611108171285743621523712879014347738499 * 10 ^ 70 +
        8278154872321032099943999925757244574435139658689031012095646355590002) * 10 ^ 70 +
        3133891593822613681401128577835144189514369790126755966418221458462800) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_37 :
    recurrence5LeadingSquare.coeff 37 =
      -(((6823311792825748433216134990559160041778947432903633169 * 10 ^ 70 +
        9856704758845087316268567269719019147026242339542326777507095879245106) * 10 ^ 70 +
        1452898995186677579023514412368027121784618657190439166256276433698766) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_38 :
    recurrence5LeadingSquare.coeff 38 =
      (((252262838340947941121246426867934016917815150984846819135 * 10 ^ 70 +
        7036238839837490045515904100493270712159976804641648968590488233734432) * 10 ^ 70 +
        9102015238730064999153948385265135604373630589988509229954057958659628) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_39 :
    recurrence5LeadingSquare.coeff 39 =
      -(((8677461952003132860629280288468824453621823584604426273606 * 10 ^ 70 +
        1707028791399602662137866481371474726314606042269950617903659088972774) * 10 ^ 70 +
        2632957488094629173937608475424822336142958099873084881313203225096360) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_40 :
    recurrence5LeadingSquare.coeff 40 =
      (((278188935006658830784545266649597175601061036099707086683535 * 10 ^ 70 +
        2828850756183086364402216807591056064662823910221437205329463292924498) * 10 ^ 70 +
        8158565338481962383458984974755161421813578672377835587578810469459776) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_41 :
    recurrence5LeadingSquare.coeff 41 =
      -(((8324977755003739809058869961504987565698721547988142766289233 * 10 ^ 70 +
        4075708565871975398905509484190658944082440717462881688120317498233511) * 10 ^ 70 +
        9376472317262271974920246236409260067820768366832272879261434185712636) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_42 :
    recurrence5LeadingSquare.coeff 42 =
      (((232903648187336280713505598744545077771356195488714222339873631 * 10 ^ 70 +
        2885172212698880977737645564552935466426948382459550539596063298178787) * 10 ^ 70 +
        3496206972275216265561180044997146643419572464018790458499689814575150) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_43 :
    recurrence5LeadingSquare.coeff 43 =
      -(((6100168386645161031992357066060388059943079752070623562649204560 * 10 ^ 70 +
        4894664494032763877270107909606746619720597827420090684509890057234730) * 10 ^ 70 +
        4194328604667375600499248433023098097945618833820496699440405684103408) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_44 :
    recurrence5LeadingSquare.coeff 44 =
      (((149786648735227754139509747009350157725283939905321312537785817962 * 10 ^ 70 +
        8216591383687223869368513278415520195059959539067408728837088204410365) * 10 ^ 70 +
        9774587627508871428981194895382439071875372428386824505098514942081518) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_45 :
    recurrence5LeadingSquare.coeff 45 =
      -(((3452526099296139923307262476956783732393354642208804382840625228104 * 10 ^ 70 +
        6225205826841227645860661061132101385870384051983578303300737642840858) * 10 ^ 70 +
        5762211155390764591887798138450365953336589167440225915542909357154364) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_46 :
    recurrence5LeadingSquare.coeff 46 =
      (((74795545669186410770879277170931471578237661275309900664781279327483 * 10 ^ 70 +
        2795127423436212618548148268919243295228661598867531975456194648420167) * 10 ^ 70 +
        0558927933181427864318815610203397368383752958675652389355853249911155) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_47 :
    recurrence5LeadingSquare.coeff 47 =
      -(((1524786477992993946320644281368691703446785335620557658301127910460244 * 10 ^ 70 +
        5904238944673588849649870747399935236424156423057274455116074704678064) * 10 ^ 70 +
        3027449748727894015955390857813011419619179497736119248768788943540942) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_48 :
    recurrence5LeadingSquare.coeff 48 =
      ((((2 * 10 ^ 70 +
        9284341665827113903694329958117830298938966955886585930911747867402316) * 10 ^ 70 +
        1738499318242770182174871645796578105207438892722195620768127491644055) * 10 ^ 70 +
        2840275800177038461925390919531912638185669421235524985540284015666518) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_49 :
    recurrence5LeadingSquare.coeff 49 =
      -((((53 * 10 ^ 70 +
        0437338330780283797978694378147885888417940029355284676437221171610210) * 10 ^ 70 +
        9611171098537597475039341486150094362931812718979733287680625091300334) * 10 ^ 70 +
        7977587953920264876959340773404555618323246487748562956874709834639106) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_50 :
    recurrence5LeadingSquare.coeff 50 =
      ((((907 * 10 ^ 70 +
        1220578398028934805845437363688986211546021578365433162135285739412773) * 10 ^ 70 +
        3355912164005470869475238160895606616632013040701734944180509253087049) * 10 ^ 70 +
        4514512205865546098913262660765109493135322941616068879919948782280530) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_51 :
    recurrence5LeadingSquare.coeff 51 =
      -((((14661 * 10 ^ 70 +
        3577007422189059772729389977732952516345653811310052968484756083967513) * 10 ^ 70 +
        7929083832409970414424872451249384373141117624084330126589640118098825) * 10 ^ 70 +
        4451363536892799257630864208014874965658134591734205138915547525848630) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_52 :
    recurrence5LeadingSquare.coeff 52 =
      ((((224175 * 10 ^ 70 +
        0779265184764499618022198609038975093547597559210588734140527135255703) * 10 ^ 70 +
        7932868251131190738031046102146757734531691433274632446417715948453631) * 10 ^ 70 +
        0931310887686385185671146285816295858586499434418923425094498971487950) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_53 :
    recurrence5LeadingSquare.coeff 53 =
      -((((3245772 * 10 ^ 70 +
        1570778507220059052630261793868160188250827889988007839172959320906871) * 10 ^ 70 +
        8484648478084850866859728567127987651005373637329480851289237897316192) * 10 ^ 70 +
        1687242499022609710259177521246585618504034381556293700915625120615252) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_54 :
    recurrence5LeadingSquare.coeff 54 =
      ((((44541525 * 10 ^ 70 +
        3911210026796171982832614282615596249100242801399129321544044137427477) * 10 ^ 70 +
        2323884555693753393422351916716850075488936705290749511654949558922938) * 10 ^ 70 +
        8969377584194964794892487023063361978547580390417561835813456042581995) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_55 :
    recurrence5LeadingSquare.coeff 55 =
      -((((579847779 * 10 ^ 70 +
        7234110011982490335916843237147277094892303223712214723856903986427553) * 10 ^ 70 +
        2957904734549857881071103728111975166845153473463500293968280015621832) * 10 ^ 70 +
        0671415892896264506455800643792745550766778085931579572194773241271678) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_56 :
    recurrence5LeadingSquare.coeff 56 =
      ((((7167004970 * 10 ^ 70 +
        2551625070526622543631054545048099321723864411202303864567939160199729) * 10 ^ 70 +
        1659184159670261361310328644851754136924196871880706939779063634873153) * 10 ^ 70 +
        6069840179308977961843344206372451646155933487881918143176824222022046) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_57 :
    recurrence5LeadingSquare.coeff 57 =
      -((((84177735763 * 10 ^ 70 +
        4950065931002682118492431222828460867215288413082232656489785201523339) * 10 ^ 70 +
        6336610302004707416899580058678610390389834096181699687875079218914873) * 10 ^ 70 +
        6398210517047391155169774926966645758292214245927533324239653895338378) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_58 :
    recurrence5LeadingSquare.coeff 58 =
      ((((940247807485 * 10 ^ 70 +
        8673127214448889457005486421608553079616235544103261480341208020917342) * 10 ^ 70 +
        5716243246130236450928851103637133566435331595380606874184791657731306) * 10 ^ 70 +
        1645214574521361479976571148273657359747739771316729076253210388363542) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_59 :
    recurrence5LeadingSquare.coeff 59 =
      -((((9995670855234 * 10 ^ 70 +
        8428681256356465810496092951623084287255232592111353134165724705977644) * 10 ^ 70 +
        3067411835920216026855178220290388504626480553992030102618252522430255) * 10 ^ 70 +
        0571683344646197261635106640954428338902401137265228399305504112837762) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_60 :
    recurrence5LeadingSquare.coeff 60 =
      ((((101212653276729 * 10 ^ 70 +
        3288678251364171398297973953869208598945948863423016461384795924503286) * 10 ^ 70 +
        5940700764176254099812562969406308386655990661717466661162601745611141) * 10 ^ 70 +
        5196908366390649934806356335495475003544414751968131848687738762064059) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_61 :
    recurrence5LeadingSquare.coeff 61 =
      -((((976854406555795 * 10 ^ 70 +
        9834000434777086677437452999966127443403400779862523932685453792586989) * 10 ^ 70 +
        7146411801198950751576949128887542168475271110815956133427472567873170) * 10 ^ 70 +
        7608502795196672317915678660101702332275358218814587451919618048646030) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_62 :
    recurrence5LeadingSquare.coeff 62 =
      ((((8993041193412524 * 10 ^ 70 +
        5047209701895950788333347539551654379651602822837909168188461697550053) * 10 ^ 70 +
        0591122693394987194841710000974247174103619447574964180094067774123367) * 10 ^ 70 +
        2178817652677759326727819170684568609183159470937902055179985056816418) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_63 :
    recurrence5LeadingSquare.coeff 63 =
      -((((79025198582382473 * 10 ^ 70 +
        1558970671506454080383413180803124281346425059815647305404383960350318) * 10 ^ 70 +
        6980053722512145014695620481144097931810958194293721631191882425812934) * 10 ^ 70 +
        3395184270587393857300111496988912603495867892051092857229936218567646) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_64 :
    recurrence5LeadingSquare.coeff 64 =
      ((((663282905525418792 * 10 ^ 70 +
        1080909044897670388383980062526477922177686397160537210858742740461830) * 10 ^ 70 +
        2509476633702444813016843077341317898096585672031958378164130886453428) * 10 ^ 70 +
        9761601601667838839552701849850688173345988287369765554485024841610133) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_65 :
    recurrence5LeadingSquare.coeff 65 =
      -((((5320958004033630051 * 10 ^ 70 +
        4450140679847873620050338787442928728665719077368872665801622250998561) * 10 ^ 70 +
        9876136717081803543076096027593865321904571195895482150392403566284757) * 10 ^ 70 +
        7065877915922485570063119650901275503014536127478986731884682624251610) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_66 :
    recurrence5LeadingSquare.coeff 66 =
      ((((40823881980749007374 * 10 ^ 70 +
        9610301959005640063542334349369970993428631680742976457843240590678438) * 10 ^ 70 +
        0384720184153804037006460598075797054549949760651611785533276998348764) * 10 ^ 70 +
        2782476272181104188131278106052514088535171839859743263930816770663836) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_67 :
    recurrence5LeadingSquare.coeff 67 =
      -((((299736835925277605586 * 10 ^ 70 +
        8301904830742079169625264190279739421823166748471452192217976102738743) * 10 ^ 70 +
        6452552838487106929805280520520146142786392082585751699385104035013801) * 10 ^ 70 +
        9711871169873390601239105875962033583347814899370952632927536620298974) : ℚ) := by
  unfold recurrence5LeadingSquare
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

theorem recurrence5LeadingSquare_coeff_68 :
    recurrence5LeadingSquare.coeff 68 =
      ((((2107306674802243679414 * 10 ^ 70 +
        2086694068018262501622284524272842676965423631857689921678870002892421) * 10 ^ 70 +
        5959112709067218441614435952686877971817240394687126403402409168094633) * 10 ^ 70 +
        0281702903099666511268698756431253849432873812116789259471054802391462) : ℚ) := by
  unfold recurrence5LeadingSquare
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

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
