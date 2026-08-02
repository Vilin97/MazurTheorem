/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupB2
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 5 lookup certificate: LeadingSquare coefficient convolution

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_160_prefix_zero :
    (∑ x ∈ Finset.range 15,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (160 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (160 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_160_suffix_zero :
    (∑ x ∈ Finset.range 15,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (160 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_160 :
    recurrence5LeadingSquare.coeff 160 =
      ((((6425423949230125903648932755058402145995 * 10 ^ 70 +
        9107689134863497149107474569475567152853703572552493817787060892285439) * 10 ^ 70 +
        9692111443874336568255908785417525571781788632011298400222528559446048) * 10 ^ 70 +
        1695695409855846280838571107239351117568182830899353138785888339600283) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 161 = 15 +
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
    rw [show 18 = 3 +
      15 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_160_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_160_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_161_prefix_zero :
    (∑ x ∈ Finset.range 16,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (161 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (161 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_161_suffix_zero :
    (∑ x ∈ Finset.range 16,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (161 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_161 :
    recurrence5LeadingSquare.coeff 161 =
      -((((4439165227384909395979681134310705614880 * 10 ^ 70 +
        4305518400676501655120854169873749122118460943762696606220395489244005) * 10 ^ 70 +
        6077159183509387126332448532244942720789745414191976429761236269844895) * 10 ^ 70 +
        7089561195275130943645016035595296673120443086303513342375978672454898) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 162 = 16 +
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
    rw [show 18 = 2 +
      16 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_161_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_161_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_162_prefix_zero :
    (∑ x ∈ Finset.range 17,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (162 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (162 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_162_suffix_zero :
    (∑ x ∈ Finset.range 17,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (162 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_162 :
    recurrence5LeadingSquare.coeff 162 =
      ((((2862948418876506653745801788398143558801 * 10 ^ 70 +
        4342033863230452447010339467086881086871772187631164157894624294651610) * 10 ^ 70 +
        6707406225299143557962287302084188272027718352585289411543086819439856) * 10 ^ 70 +
        1104597810074096565192150631021927996120120782134180574478000319646749) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 163 = 17 +
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
    rw [show 18 = 1 +
      17 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_162_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_162_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_163_prefix_zero :
    (∑ x ∈ Finset.range 18,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (163 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (163 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_163_suffix_zero :
    (∑ x ∈ Finset.range 18,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (163 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_163 :
    recurrence5LeadingSquare.coeff 163 =
      -((((1718760669647621934457635887627495546826 * 10 ^ 70 +
        8010589723365189467712662890660231554153914974349373823223014157220859) * 10 ^ 70 +
        6826436096434461271121827639866567359541582514959621843922423633577687) * 10 ^ 70 +
        6620390704950750829584628062835901831109739496861602322838592626174502) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 164 = 18 +
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
  rw [recurrence5LeadingSquare_coeff_163_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_163_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_164_prefix_zero :
    (∑ x ∈ Finset.range 19,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (164 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (164 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_164_suffix_zero :
    (∑ x ∈ Finset.range 19,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (164 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_164 :
    recurrence5LeadingSquare.coeff 164 =
      ((((950360649181440196787856212102513960515 * 10 ^ 70 +
        4922588523308735299202125901044942987429895923875629863193172503236119) * 10 ^ 70 +
        7235924378117600869187492313142522813413437286979279745567607607703625) * 10 ^ 70 +
        3529559605903812383817924124833149140331345148400672705753696155551413) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 165 = 19 +
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
    rw [show 50 = 31 +
      19 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_164_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_164_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_165_prefix_zero :
    (∑ x ∈ Finset.range 20,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (165 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (165 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_165_suffix_zero :
    (∑ x ∈ Finset.range 20,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (165 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_165 :
    recurrence5LeadingSquare.coeff 165 =
      -((((472185808235271262756186925677547502532 * 10 ^ 70 +
        0988094917608214506573925474935877886002906680141254573053614710149737) * 10 ^ 70 +
        7229153200723636308385539327574348138592983570809082928468330711985373) * 10 ^ 70 +
        1024940422331961560406631149698721425176699147531766941869453546405162) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 166 = 20 +
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
    rw [show 50 = 30 +
      20 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_165_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_165_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_166_prefix_zero :
    (∑ x ∈ Finset.range 21,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (166 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (166 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_166_suffix_zero :
    (∑ x ∈ Finset.range 21,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (166 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_166 :
    recurrence5LeadingSquare.coeff 166 =
      ((((198473809856514260977179898504399251642 * 10 ^ 70 +
        4664221899172317483702543756774539866296343774917064591659377727214819) * 10 ^ 70 +
        5047820751052134299293664638875141825523225726188791213640090518221088) * 10 ^ 70 +
        9470103012563412811990731853576447100913699281602289306409050182252917) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 167 = 21 +
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
    rw [show 50 = 29 +
      21 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_166_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_166_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_167_prefix_zero :
    (∑ x ∈ Finset.range 22,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (167 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (167 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_167_suffix_zero :
    (∑ x ∈ Finset.range 22,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (167 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_167 :
    recurrence5LeadingSquare.coeff 167 =
      -((((57348314656454286510136904001766476954 * 10 ^ 70 +
        7635818327874081938885181900985866615462079902096739492506268553936779) * 10 ^ 70 +
        9347618081347566440576935883778225740629175710423182891998190751387076) * 10 ^ 70 +
        1203163290567526117717258243248490922452043623183140855475767942977572) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 168 = 22 +
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
    rw [show 50 = 28 +
      22 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_167_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_167_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_168_prefix_zero :
    (∑ x ∈ Finset.range 23,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (168 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (168 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_168_suffix_zero :
    (∑ x ∈ Finset.range 23,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (168 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_168 :
    recurrence5LeadingSquare.coeff 168 =
      -((((4850875657633937525174223265274474112 * 10 ^ 70 +
        3661885233440753027850648712825927221966809664198476881890906254842307) * 10 ^ 70 +
        4533014456819735322424291187878816535135525148758918899487301630641325) * 10 ^ 70 +
        7273880548539815923683969208289868478661582884344339164704785869331003) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 169 = 23 +
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
    rw [show 50 = 27 +
      23 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_168_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_168_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_169_prefix_zero :
    (∑ x ∈ Finset.range 24,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (169 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (169 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_169_suffix_zero :
    (∑ x ∈ Finset.range 24,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (169 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_169 :
    recurrence5LeadingSquare.coeff 169 =
      ((((24615942181231766299028633526388173920 * 10 ^ 70 +
        9561176326598032389717625834784555820885938745271096265097369547749113) * 10 ^ 70 +
        3541754712078090031101573963006337363666933311634486150377849289219076) * 10 ^ 70 +
        9861906952212343740275334104439705744005616834237670203744920524348488) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 170 = 24 +
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
    rw [show 50 = 26 +
      24 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_169_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_169_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_170_prefix_zero :
    (∑ x ∈ Finset.range 25,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (170 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (170 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_170_suffix_zero :
    (∑ x ∈ Finset.range 25,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (170 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_170 :
    recurrence5LeadingSquare.coeff 170 =
      -((((24647256487682943410519813583641724372 * 10 ^ 70 +
        1111040886867031015905937880231415460607001789474983736284642829085845) * 10 ^ 70 +
        9806290932125339572595383447102674766996408875649768634767002196825975) * 10 ^ 70 +
        9175458875277999246537784248988738926649355122780990078619021555532972) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 171 = 25 +
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
    rw [show 50 = 25 +
      25 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_170_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_170_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_171_prefix_zero :
    (∑ x ∈ Finset.range 26,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (171 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (171 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_171_suffix_zero :
    (∑ x ∈ Finset.range 26,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (171 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_171 :
    recurrence5LeadingSquare.coeff 171 =
      ((((17723699993655050235792702262561538657 * 10 ^ 70 +
        2422709063100780003144839402528979125599548729391550640337406032380337) * 10 ^ 70 +
        2789388522391368185123376393371781940632992389093782968735470102228561) * 10 ^ 70 +
        1743229797830557100652799772065644868162926124911655020653810528872274) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 172 = 26 +
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
    rw [show 50 = 24 +
      26 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_171_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_171_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_172_prefix_zero :
    (∑ x ∈ Finset.range 27,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (172 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (172 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_172_suffix_zero :
    (∑ x ∈ Finset.range 27,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (172 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_172 :
    recurrence5LeadingSquare.coeff 172 =
      -((((10136771069821366023074794745634793513 * 10 ^ 70 +
        5443428216379032827218174770543859577710606924683670152865447569029513) * 10 ^ 70 +
        3639660650627585271536311273721521695590355069527122567961039597957641) * 10 ^ 70 +
        6798693109361303826513180862217053931991634917379503490626532955536119) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 173 = 27 +
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
    rw [show 50 = 23 +
      27 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_172_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_172_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_173_prefix_zero :
    (∑ x ∈ Finset.range 28,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (173 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (173 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_173_suffix_zero :
    (∑ x ∈ Finset.range 28,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (173 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_173 :
    recurrence5LeadingSquare.coeff 173 =
      ((((4337847301530408592354699196359107953 * 10 ^ 70 +
        6769084747528890704401761030870446837386104295742300863825961385452838) * 10 ^ 70 +
        4984119648767122936746765772398155789943809095884195316789890933222975) * 10 ^ 70 +
        8066341704349482871163850270409758540159506919102501152740603555633830) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 174 = 28 +
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
    rw [show 50 = 22 +
      28 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_173_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_173_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_174_prefix_zero :
    (∑ x ∈ Finset.range 29,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (174 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (174 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_174_suffix_zero :
    (∑ x ∈ Finset.range 29,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (174 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_174 :
    recurrence5LeadingSquare.coeff 174 =
      -((((772501120042886170381660363928076186 * 10 ^ 70 +
        7033381953269621392031931799538442093595975730160531758533088811658295) * 10 ^ 70 +
        6093341422210669211651973145106379831170017344382360881639973671719575) * 10 ^ 70 +
        0917239562732953543710203152307014276464243152038167645578757776469335) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 175 = 29 +
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
    rw [show 50 = 21 +
      29 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_174_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_174_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_175_prefix_zero :
    (∑ x ∈ Finset.range 30,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (175 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (175 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_175_suffix_zero :
    (∑ x ∈ Finset.range 30,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (175 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_175 :
    recurrence5LeadingSquare.coeff 175 =
      -((((971586699118649096533545109847260902 * 10 ^ 70 +
        7247387351601115832200636951463816346319223483864751683129026636786115) * 10 ^ 70 +
        5555701086910947793832710380306527883253768686527126024821765346456457) * 10 ^ 70 +
        6096273620797176604049789593774549946380982625488903490368168588952876) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 176 = 30 +
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
    rw [show 50 = 20 +
      30 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_175_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_175_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_176_prefix_zero :
    (∑ x ∈ Finset.range 31,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (176 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (176 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_176_suffix_zero :
    (∑ x ∈ Finset.range 31,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (176 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_176 :
    recurrence5LeadingSquare.coeff 176 =
      ((((1527084401301375530812756696332130064 * 10 ^ 70 +
        7165409391883242628920857401336100436389924952632070968389870348643091) * 10 ^ 70 +
        4741987304383025039222702276706531217681563622772267367260186084831545) * 10 ^ 70 +
        3487430522570172171158383404427286751508510317942296675439722981980879) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 177 = 31 +
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
    rw [show 50 = 19 +
      31 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_176_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_176_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_177_prefix_zero :
    (∑ x ∈ Finset.range 32,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (177 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (177 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_177_suffix_zero :
    (∑ x ∈ Finset.range 32,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (177 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_177 :
    recurrence5LeadingSquare.coeff 177 =
      -((((1449794278216691863206650677442525486 * 10 ^ 70 +
        1755825257447273795969817556793885648245126127830486568632214670525352) * 10 ^ 70 +
        8686466292939333499053130658846037868278792193167565833312307578357528) * 10 ^ 70 +
        4974187613406874241846333192644480624735359556392183766044137517477004) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 178 = 32 +
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
    rw [show 50 = 18 +
      32 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_177_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_177_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_178_prefix_zero :
    (∑ x ∈ Finset.range 33,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (178 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (178 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_178_suffix_zero :
    (∑ x ∈ Finset.range 33,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (178 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_178 :
    recurrence5LeadingSquare.coeff 178 =
      ((((1123123947603098363254553577225348750 * 10 ^ 70 +
        5519246331098613678920585601862659273095777067364448702800470929307197) * 10 ^ 70 +
        0632373757505121453589629101136792795864568457899393004367174919760126) * 10 ^ 70 +
        7795760738909128126333830361997867966544183035428770420967691888760616) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 179 = 33 +
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
    rw [show 50 = 17 +
      33 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_178_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_178_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_179_prefix_zero :
    (∑ x ∈ Finset.range 34,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (179 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (179 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_179_suffix_zero :
    (∑ x ∈ Finset.range 34,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (179 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_179 :
    recurrence5LeadingSquare.coeff 179 =
      -((((764495114649890410957690948906132155 * 10 ^ 70 +
        4113204358121422032546275255887848955746926390718993983937963880804406) * 10 ^ 70 +
        7924773051677050131734033525006201510919380757869296223071534313767912) * 10 ^ 70 +
        4502380407099773523545544399637704346797796373518315887734878763299960) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 180 = 34 +
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
    rw [show 50 = 16 +
      34 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_179_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_179_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_180_prefix_zero :
    (∑ x ∈ Finset.range 35,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (180 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (180 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_180_suffix_zero :
    (∑ x ∈ Finset.range 35,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (180 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_180 :
    recurrence5LeadingSquare.coeff 180 =
      ((((470240981518705010352951422111349966 * 10 ^ 70 +
        4195325043993749746927302253358838779840727075232260761594831597735088) * 10 ^ 70 +
        9936872674722504249308553894983483162970436495133542600197117576890675) * 10 ^ 70 +
        3451823172165493800332335695638856520070621007843943167646564419812948) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 181 = 35 +
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
    rw [show 50 = 15 +
      35 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_180_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_180_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_181_prefix_zero :
    (∑ x ∈ Finset.range 36,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (181 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (181 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_181_suffix_zero :
    (∑ x ∈ Finset.range 36,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (181 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_181 :
    recurrence5LeadingSquare.coeff 181 =
      -((((264329563572976696963147303246285676 * 10 ^ 70 +
        8123569060404396708844396919642970846779238537128699460264242951530834) * 10 ^ 70 +
        2086593299171644101847355594512204553922942053249266422709049112777511) * 10 ^ 70 +
        0891619002008047795728002564328133279047363764795413330748531375361494) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 182 = 36 +
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
    rw [show 50 = 14 +
      36 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_181_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_181_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_182_prefix_zero :
    (∑ x ∈ Finset.range 37,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (182 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (182 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_182_suffix_zero :
    (∑ x ∈ Finset.range 37,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (182 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_182 :
    recurrence5LeadingSquare.coeff 182 =
      ((((136094685096977444854166396467567873 * 10 ^ 70 +
        6115575661953175521698109038307176765239539961016235293763834271492079) * 10 ^ 70 +
        4122839101605423350098952092997367887833479199314167013152312074639062) * 10 ^ 70 +
        8475245818269039747663641128604509013762952199817834129477970362397775) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 183 = 37 +
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
    rw [show 50 = 13 +
      37 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_182_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_182_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_183_prefix_zero :
    (∑ x ∈ Finset.range 38,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (183 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (183 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_183_suffix_zero :
    (∑ x ∈ Finset.range 38,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (183 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_183 :
    recurrence5LeadingSquare.coeff 183 =
      -((((63868093960684847454282813095694700 * 10 ^ 70 +
        4397053136926962208643106089697223298995707036462979393509930588388571) * 10 ^ 70 +
        2093101928877046340501684548125957689274299748555280011306530787929242) * 10 ^ 70 +
        4909790030153828021272485981672953897513694813127827871761808744980768) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 184 = 38 +
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
    rw [show 50 = 12 +
      38 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_183_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_183_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_184_prefix_zero :
    (∑ x ∈ Finset.range 39,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (184 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (184 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_184_suffix_zero :
    (∑ x ∈ Finset.range 39,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (184 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_184 :
    recurrence5LeadingSquare.coeff 184 =
      ((((26945838065508253792564806073219029 * 10 ^ 70 +
        5561008263949047550841438856291961932595339515462800613769412953949822) * 10 ^ 70 +
        9714171260973356925688032651557874633748403025531513092972643466945980) * 10 ^ 70 +
        4554749183260100408068992549168305880333192115880746955349797618333052) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 185 = 39 +
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
    rw [show 50 = 11 +
      39 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_184_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_184_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_185_prefix_zero :
    (∑ x ∈ Finset.range 40,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (185 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (185 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_185_suffix_zero :
    (∑ x ∈ Finset.range 40,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (185 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_185 :
    recurrence5LeadingSquare.coeff 185 =
      -((((9919408325809655371983712446302507 * 10 ^ 70 +
        3098056648336627284983651009600198545955780441747063762290043158737618) * 10 ^ 70 +
        6505388120873342234367750058959592504618518071433468827664640147408410) * 10 ^ 70 +
        3861636299944094868397022411197130988548070871260037334287272277637800) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 186 = 40 +
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
    rw [show 50 = 10 +
      40 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_185_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_185_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_186_prefix_zero :
    (∑ x ∈ Finset.range 41,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (186 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (186 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_186_suffix_zero :
    (∑ x ∈ Finset.range 41,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (186 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_186 :
    recurrence5LeadingSquare.coeff 186 =
      ((((2967448466249035428556383489000030 * 10 ^ 70 +
        5188162915108352378794413492229904467090873386884842174139402114581264) * 10 ^ 70 +
        0005503229074058779638023591381437701088270798720012862172136849110554) * 10 ^ 70 +
        2905538545933122631318885923117277407730732967089871148836053253452339) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 187 = 41 +
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
    rw [show 50 = 9 +
      41 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_186_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_186_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_187_prefix_zero :
    (∑ x ∈ Finset.range 42,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (187 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (187 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_187_suffix_zero :
    (∑ x ∈ Finset.range 42,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (187 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_187 :
    recurrence5LeadingSquare.coeff 187 =
      -((((563156535326957223376422444119698 * 10 ^ 70 +
        0397985797411772127885081147308318211148351617090766281018658582266438) * 10 ^ 70 +
        4034463789857273957313605882886127629991564967811390066885978346157137) * 10 ^ 70 +
        2949162906072418599531817932887482913151126633070603884387941886157710) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 188 = 42 +
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
    rw [show 50 = 8 +
      42 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_187_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_187_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_188_prefix_zero :
    (∑ x ∈ Finset.range 43,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (188 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (188 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_188_suffix_zero :
    (∑ x ∈ Finset.range 43,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (188 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_188 :
    recurrence5LeadingSquare.coeff 188 =
      -((((57305697164852468745897396574251 * 10 ^ 70 +
        8536540842346309279154144086400067772278270501772690953446170442796367) * 10 ^ 70 +
        9381810029238834776882118635213418195635582994435229187214962529635630) * 10 ^ 70 +
        9829441148395651582962173443193867135649412017262941482196052300131110) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 189 = 43 +
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
    rw [show 50 = 7 +
      43 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_188_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_188_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_189_prefix_zero :
    (∑ x ∈ Finset.range 44,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (189 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (189 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_189_suffix_zero :
    (∑ x ∈ Finset.range 44,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (189 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_189 :
    recurrence5LeadingSquare.coeff 189 =
      ((((109415433767492921484401829492976 * 10 ^ 70 +
        9466003016425338174055725158692667301088852439514267675406443471478551) * 10 ^ 70 +
        3762558631473380099234593513848349489246460766761713170293094921588577) * 10 ^ 70 +
        8280722152329515743525974277388666828046091196961963589959322921071648) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 190 = 44 +
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
    rw [show 50 = 6 +
      44 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_189_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_189_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_190_prefix_zero :
    (∑ x ∈ Finset.range 45,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (190 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (190 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_190_suffix_zero :
    (∑ x ∈ Finset.range 45,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (190 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_190 :
    recurrence5LeadingSquare.coeff 190 =
      -((((46771800549827266353163172634838 * 10 ^ 70 +
        6104624482616314469036113274895200074706453023796327427868124826897633) * 10 ^ 70 +
        3488923469880891157767347781162631885318397170990192378981357505332718) * 10 ^ 70 +
        7359789764964832455756070690319859400950409525094939156856129544573870) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 191 = 45 +
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
    rw [show 50 = 5 +
      45 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_190_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_190_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_191_prefix_zero :
    (∑ x ∈ Finset.range 46,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (191 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (191 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_191_suffix_zero :
    (∑ x ∈ Finset.range 46,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (191 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_191 :
    recurrence5LeadingSquare.coeff 191 =
      -((((1518218411610012736610964251804 * 10 ^ 70 +
        0857504151331239220892587356727778367571078301325235292559993977074076) * 10 ^ 70 +
        0359079653815481249227096722606317825598717545587680742894271702393416) * 10 ^ 70 +
        3288412638379560804517140607826908888391729682482307967786864872238108) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 192 = 46 +
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
    rw [show 50 = 4 +
      46 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_191_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_191_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_192_prefix_zero :
    (∑ x ∈ Finset.range 47,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (192 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (192 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_192_suffix_zero :
    (∑ x ∈ Finset.range 47,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (192 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_192 :
    recurrence5LeadingSquare.coeff 192 =
      ((((20035942949914707870622949514886 * 10 ^ 70 +
        3877994478758845193140012307932656552891918201448906815983108469298927) * 10 ^ 70 +
        0959433132760148511742548018277602923921712522118024785316340466061122) * 10 ^ 70 +
        9699542523152283146570332271478011651578344762781051170514929132963764) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 193 = 47 +
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
    rw [show 50 = 3 +
      47 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_192_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_192_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_193_prefix_zero :
    (∑ x ∈ Finset.range 48,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (193 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (193 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_193_suffix_zero :
    (∑ x ∈ Finset.range 48,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (193 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_193 :
    recurrence5LeadingSquare.coeff 193 =
      -((((20752150461589044147011438194726 * 10 ^ 70 +
        5063267210990641615171920691174185309507178270474945919646780346572539) * 10 ^ 70 +
        6679906074862077320785090323671120773976389247902542538296410656252711) * 10 ^ 70 +
        1955008446805265794987318195084715257960021494328831202050434142961136) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 194 = 48 +
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
    rw [show 50 = 2 +
      48 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_193_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_193_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_194_prefix_zero :
    (∑ x ∈ Finset.range 49,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (194 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (194 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_194_suffix_zero :
    (∑ x ∈ Finset.range 49,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (194 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_194 :
    recurrence5LeadingSquare.coeff 194 =
      ((((15178500374983483554262274701318 * 10 ^ 70 +
        2377649184698535953781744587670487054796783430173857114232521117284435) * 10 ^ 70 +
        6126231204830301007614497604769037573487123396435462579408520367534162) * 10 ^ 70 +
        3747051611586087410613057885454835753705021518531850712263544696225443) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 195 = 49 +
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
    rw [show 50 = 1 +
      49 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_194_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_194_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_195_prefix_zero :
    (∑ x ∈ Finset.range 50,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (195 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (195 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_195_suffix_zero :
    (∑ x ∈ Finset.range 50,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (195 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_195 :
    recurrence5LeadingSquare.coeff 195 =
      -((((9294831266591315350088940417749 * 10 ^ 70 +
        9324338414913948022002938164038591678483804415713493261225588872559347) * 10 ^ 70 +
        1785994110798206160407883414621684880117047693568509593943403052142198) * 10 ^ 70 +
        4536015865724733425051570819895713480118980345908855197693111453412712) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 196 = 50 +
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
  rw [recurrence5LeadingSquare_coeff_195_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_195_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_196_prefix_zero :
    (∑ x ∈ Finset.range 51,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (196 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (196 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_196_suffix_zero :
    (∑ x ∈ Finset.range 51,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (196 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_196 :
    recurrence5LeadingSquare.coeff 196 =
      ((((5049483288546871965505697155193 * 10 ^ 70 +
        1150225498553959005987996271086689148886835884811032491115940987659354) * 10 ^ 70 +
        6775617667870017512103550669956429329720952166741176191276844103351342) * 10 ^ 70 +
        1419276262716597254735310735191508025801043031581220963232439096454002) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 197 = 51 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 31 +
      51 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_196_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_196_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_197_prefix_zero :
    (∑ x ∈ Finset.range 52,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (197 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (197 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_197_suffix_zero :
    (∑ x ∈ Finset.range 52,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (197 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_197 :
    recurrence5LeadingSquare.coeff 197 =
      -((((2501220017928891549454046015972 * 10 ^ 70 +
        4913134468005643561371673837800955004991029862612884239608433772037017) * 10 ^ 70 +
        9776018170652392568844714906868043902620643033012940781369597490254093) * 10 ^ 70 +
        7020219206023952361296304267029318552411376595660629602894365608646498) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 198 = 52 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 30 +
      52 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_197_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_197_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_198_prefix_zero :
    (∑ x ∈ Finset.range 53,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (198 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (198 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_198_suffix_zero :
    (∑ x ∈ Finset.range 53,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (198 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_198 :
    recurrence5LeadingSquare.coeff 198 =
      ((((1147061609157469137530491668612 * 10 ^ 70 +
        7226631887511495590496071116242538069923343896489885738338452218407341) * 10 ^ 70 +
        8273506685043791761229861437283523399227026192062484582972197058604853) * 10 ^ 70 +
        8010727591921792896496335814707563398390887809871420687642997914505660) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 199 = 53 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 29 +
      53 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_198_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_198_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_199_prefix_zero :
    (∑ x ∈ Finset.range 54,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (199 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (199 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_199_suffix_zero :
    (∑ x ∈ Finset.range 54,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (199 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_199 :
    recurrence5LeadingSquare.coeff 199 =
      -((((491577514076117302202282675818 * 10 ^ 70 +
        1730304685388622120675000460021599174088459451948823465142022111134330) * 10 ^ 70 +
        2610614973501436611332082502829307813759858235765802646613593279360146) * 10 ^ 70 +
        0420956756164451914676801165427914068581350353609648097458755078136170) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 200 = 54 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 28 +
      54 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_199_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_199_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_200_prefix_zero :
    (∑ x ∈ Finset.range 55,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (200 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (200 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_200_suffix_zero :
    (∑ x ∈ Finset.range 55,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (200 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_200 :
    recurrence5LeadingSquare.coeff 200 =
      ((((198061891235925932342495473408 * 10 ^ 70 +
        9498084747865778350428522699530840314496334967654736545677959389938271) * 10 ^ 70 +
        4060533160980235953319451124462569648552625524265600338456728420002951) * 10 ^ 70 +
        4369514320755732654172966548694207973111417342657529628469807955600372) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 201 = 55 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 27 +
      55 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_200_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_200_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_201_prefix_zero :
    (∑ x ∈ Finset.range 56,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (201 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (201 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_201_suffix_zero :
    (∑ x ∈ Finset.range 56,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (201 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_201 :
    recurrence5LeadingSquare.coeff 201 =
      -((((75374806401241770691336945920 * 10 ^ 70 +
        8136194246935749697845272971780203811634572789704324093509860238368579) * 10 ^ 70 +
        5270950114756954897152770141244983112998371095563951482102167547796540) * 10 ^ 70 +
        0291229543040602358006500223778478877876031474532683249708895806370654) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 202 = 56 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 26 +
      56 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_201_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_201_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_202_prefix_zero :
    (∑ x ∈ Finset.range 57,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (202 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (202 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_202_suffix_zero :
    (∑ x ∈ Finset.range 57,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (202 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_202 :
    recurrence5LeadingSquare.coeff 202 =
      ((((27246209422624684572014583259 * 10 ^ 70 +
        8704846309328100879089028718175822185892250636333908276775542477334071) * 10 ^ 70 +
        9581223980950219137882133706792782665083922800020252469699766910955064) * 10 ^ 70 +
        4396671401494548121682371385494100122914578361098441664510140702762708) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 203 = 57 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 25 +
      57 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_202_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_202_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_203_prefix_zero :
    (∑ x ∈ Finset.range 58,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (203 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (203 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_203_suffix_zero :
    (∑ x ∈ Finset.range 58,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (203 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_203 :
    recurrence5LeadingSquare.coeff 203 =
      -((((9463565549019506074240843163 * 10 ^ 70 +
        9487186530062638495392676241163114506114503301770975937143156023087785) * 10 ^ 70 +
        7869170012351730535573810900159756680126190671677527918336734284063029) * 10 ^ 70 +
        8559220364539495311079620500158108742145378527706177144738079951370516) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 204 = 58 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 24 +
      58 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_203_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_203_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_204_prefix_zero :
    (∑ x ∈ Finset.range 59,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (204 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (204 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_204_suffix_zero :
    (∑ x ∈ Finset.range 59,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (204 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_204 :
    recurrence5LeadingSquare.coeff 204 =
      ((((3246923460286435711243066142 * 10 ^ 70 +
        1366542451719113800137672014268648134717964761316328906024822519609445) * 10 ^ 70 +
        2805183105578747958801565378929487184439316876416024692242755532811224) * 10 ^ 70 +
        6182849751980187546093161211854967819215143474890930079530937464666635) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 205 = 59 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 23 +
      59 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_204_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_204_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_205_prefix_zero :
    (∑ x ∈ Finset.range 60,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (205 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (205 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_205_suffix_zero :
    (∑ x ∈ Finset.range 60,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (205 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_205 :
    recurrence5LeadingSquare.coeff 205 =
      -((((1165478500197750514662113449 * 10 ^ 70 +
        7428279907055748164111838427938518641002043566895287684627043240902796) * 10 ^ 70 +
        7512873118209372292773330230139062373167550185164154315658899977514040) * 10 ^ 70 +
        9665809487191578643807817299874448498108157737705508462172607240992140) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 206 = 60 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 22 +
      60 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_205_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_205_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_206_prefix_zero :
    (∑ x ∈ Finset.range 61,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (206 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (206 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_206_suffix_zero :
    (∑ x ∈ Finset.range 61,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (206 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_206 :
    recurrence5LeadingSquare.coeff 206 =
      ((((474336807998118984160420137 * 10 ^ 70 +
        8521885588073118226501008905989863782682420700415625693030633588566042) * 10 ^ 70 +
        8430178405693829294343499355070145536576987925821349816252350738006633) * 10 ^ 70 +
        2315164955022320746962956844926789269664563444354179981555945219519716) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 207 = 61 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 21 +
      61 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_206_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_206_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_207_prefix_zero :
    (∑ x ∈ Finset.range 62,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (207 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (207 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_207_suffix_zero :
    (∑ x ∈ Finset.range 62,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (207 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_207 :
    recurrence5LeadingSquare.coeff 207 =
      -((((228175589138297078411983195 * 10 ^ 70 +
        0917942282916937152192971729686404430180843362819896698723672178922835) * 10 ^ 70 +
        3375922620329857764213557868197207252363554960347791065233544497818279) * 10 ^ 70 +
        7699361652400178740207099568983679985419419019250021169869370078313648) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 208 = 62 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 20 +
      62 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_207_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_207_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_208_prefix_zero :
    (∑ x ∈ Finset.range 63,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (208 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (208 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_208_suffix_zero :
    (∑ x ∈ Finset.range 63,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (208 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_208 :
    recurrence5LeadingSquare.coeff 208 =
      ((((123912923728941848226725876 * 10 ^ 70 +
        1733436447879476131548531791562642172209930178966186798969947298558057) * 10 ^ 70 +
        0837176470971634435251854907177802789574540888678467174283290607068894) * 10 ^ 70 +
        0222333623178034138197213722372158702007042785378554077942770718731528) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 209 = 63 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 19 +
      63 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_208_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_208_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_209_prefix_zero :
    (∑ x ∈ Finset.range 64,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (209 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (209 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_209_suffix_zero :
    (∑ x ∈ Finset.range 64,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (209 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_209 :
    recurrence5LeadingSquare.coeff 209 =
      -((((70100544410516239848470800 * 10 ^ 70 +
        5130404648657893790504567323768439600378473335142927028722229087174900) * 10 ^ 70 +
        2882913726861117023791105416149378694389788911306676299479547038688187) * 10 ^ 70 +
        5599082763576696874021963140059410508655793684132236863762243814417840) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 210 = 64 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 18 +
      64 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_209_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_209_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_210_prefix_zero :
    (∑ x ∈ Finset.range 65,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (210 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (210 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_210_suffix_zero :
    (∑ x ∈ Finset.range 65,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (210 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_210 :
    recurrence5LeadingSquare.coeff 210 =
      ((((39105907149812825762747511 * 10 ^ 70 +
        0360368187665813272597707905406469221799486486533310163989885352764200) * 10 ^ 70 +
        1373190167725137616049953796197824449382294340719723958740517920958900) * 10 ^ 70 +
        8115489125989224414751412210322221279582727167407877376835005849835440) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 211 = 65 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 17 +
      65 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_210_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_210_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_211_prefix_zero :
    (∑ x ∈ Finset.range 66,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (211 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (211 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_211_suffix_zero :
    (∑ x ∈ Finset.range 66,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (211 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_211 :
    recurrence5LeadingSquare.coeff 211 =
      -((((20994629118224934827213970 * 10 ^ 70 +
        0673641107191032933427485286392779506340768883163812629235757287301501) * 10 ^ 70 +
        5165079766987216177241276543262321219320015924255313110350176577166833) * 10 ^ 70 +
        0892711549142460103875287857335634482629335063021032749722272196085060) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 212 = 66 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 16 +
      66 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_211_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_211_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_212_prefix_zero :
    (∑ x ∈ Finset.range 67,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (212 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (212 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_212_suffix_zero :
    (∑ x ∈ Finset.range 67,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (212 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_212 :
    recurrence5LeadingSquare.coeff 212 =
      ((((10767008320033385746546252 * 10 ^ 70 +
        6501966401112609053166131724117738566689211411467315368448435296413820) * 10 ^ 70 +
        4515558740072963403706929589484915288010430984672230766027917880558084) * 10 ^ 70 +
        6297170034904554243399407129653858179371651149196417890738479381497483) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 213 = 67 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 15 +
      67 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_212_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_212_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_213_prefix_zero :
    (∑ x ∈ Finset.range 68,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (213 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (213 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_213_suffix_zero :
    (∑ x ∈ Finset.range 68,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (213 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_213 :
    recurrence5LeadingSquare.coeff 213 =
      -((((5273555039819055791058267 * 10 ^ 70 +
        0732850789538346652663696197686623878791534075323476983052920829428264) * 10 ^ 70 +
        0137599547612874360076864334063659991286588278856612314537331053577577) * 10 ^ 70 +
        8666505306986162141372673341775816118215310013927234320083335906162544) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 214 = 68 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 14 +
      68 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_213_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_213_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_214_prefix_zero :
    (∑ x ∈ Finset.range 69,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (214 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (214 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_214_suffix_zero :
    (∑ x ∈ Finset.range 69,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (214 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_214 :
    recurrence5LeadingSquare.coeff 214 =
      ((((2472659973898489151797243 * 10 ^ 70 +
        1099637456122381620108709620491250925647797335641806979304861270190094) * 10 ^ 70 +
        9188807008793619418666231061594128353507129831488293219737143810961488) * 10 ^ 70 +
        4025630494587969935303831513815379728661395299735649010960651706527615) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 215 = 69 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 13 +
      69 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_214_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_214_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_215_prefix_zero :
    (∑ x ∈ Finset.range 70,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (215 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (215 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_215_suffix_zero :
    (∑ x ∈ Finset.range 70,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (215 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_215 :
    recurrence5LeadingSquare.coeff 215 =
      -((((1113285844235815162880225 * 10 ^ 70 +
        7701074253687219398787347020629062687382176276942535024055510091530704) * 10 ^ 70 +
        6628284258263235937642365790573510646858989025807932307684281326709298) * 10 ^ 70 +
        0073727431314654348585258082613612890013175692434384037942064125531966) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 216 = 70 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 12 +
      70 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_215_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_215_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_216_prefix_zero :
    (∑ x ∈ Finset.range 71,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (216 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (216 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_216_suffix_zero :
    (∑ x ∈ Finset.range 71,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (216 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_216 :
    recurrence5LeadingSquare.coeff 216 =
      ((((482749234360082379960423 * 10 ^ 70 +
        2819320076373015599661394038816459034988387319472092697501036609444159) * 10 ^ 70 +
        2779016428878154623917981749351453710393099727035669463347530881810990) * 10 ^ 70 +
        4345700088605309616109067712494757771498328951139028606562785637946689) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 217 = 71 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 11 +
      71 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_216_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_216_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5LeadingSquare_coeff_217_prefix_zero :
    (∑ x ∈ Finset.range 72,
      remainder6Coefficient2.coeff x * remainder6Coefficient2.coeff (217 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (217 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5LeadingSquare_coeff_217_suffix_zero :
    (∑ x ∈ Finset.range 72,
      remainder6Coefficient2.coeff (146 + x) *
        remainder6Coefficient2.coeff (217 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5LeadingSquare_coeff_217 :
    recurrence5LeadingSquare.coeff 217 =
      -((((202128893669259090276436 * 10 ^ 70 +
        2504291822283139603997043669949998444186432705585959735714699552506212) * 10 ^ 70 +
        8268987706097628426876675143272167467478087565081278385727016719752594) * 10 ^ 70 +
        8086221394872808065754583152285053814818585607405037152708002809829220) : ℚ) := by
  unfold recurrence5LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 218 = 72 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 10 +
      72 by norm_num, Finset.sum_range_add]
  rw [recurrence5LeadingSquare_coeff_217_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5LeadingSquare_coeff_217_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
