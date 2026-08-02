/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData2
import Mathlib.Tactic.NormNum

/-!
# Recurrence 2 lookup certificate: B1 source coefficients, high half

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence2B1_coeff_76 :
    remainder3Coefficient1.coeff 76 =
      -((212826330 * 10 ^ 70 +
        4031884661937019467836098476351233112952289169889106497748167260011030) : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_77 :
    remainder3Coefficient1.coeff 77 =
      -((465549535 * 10 ^ 70 +
        3986032186065426927710087414336309004684723029863946850736938569625470) : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_78 :
    remainder3Coefficient1.coeff 78 =
      ((3589841132 * 10 ^ 70 +
        2509749145087380687419441693370113656410088735179449966192125074667166) : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_79 :
    remainder3Coefficient1.coeff 79 =
      -((13280748920 * 10 ^ 70 +
        5616938214087373211656968748336618338539107970071507094374846674034578) : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_80 :
    remainder3Coefficient1.coeff 80 =
      ((37729778200 * 10 ^ 70 +
        7846935177266198251874381768322066955561437899269398642594015570946741) : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_81 :
    remainder3Coefficient1.coeff 81 =
      -((91008978753 * 10 ^ 70 +
        5213108242479439382101488926979837879483752938352754073706839987198819) : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_82 :
    remainder3Coefficient1.coeff 82 =
      ((194086074760 * 10 ^ 70 +
        9479118472499378373889364781727332852944916344459635046703292995638723) : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_83 :
    remainder3Coefficient1.coeff 83 =
      -((373732706816 * 10 ^ 70 +
        7475407120959320383631772753032800758325034742116172764465373878107207) : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_84 :
    remainder3Coefficient1.coeff 84 =
      ((658083737007 * 10 ^ 70 +
        8895186182865630996867775025095116301893879243303286625890166627309004) : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_85 :
    remainder3Coefficient1.coeff 85 =
      -((1068493200125 * 10 ^ 70 +
        3622988142023115532959049080061802093752970417816761078591499250807254) : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_86 :
    remainder3Coefficient1.coeff 86 =
      ((1609022714833 * 10 ^ 70 +
        2951542696197760384989426594002642638355335420759508825440104240254130) : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_87 :
    remainder3Coefficient1.coeff 87 =
      -((2256812556772 * 10 ^ 70 +
        6506501385985517247895190314001236330498499045126621688603772909592417) : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_88 :
    remainder3Coefficient1.coeff 88 =
      ((2957686618994 * 10 ^ 70 +
        8908515337294370596665858607544127164362644311738506511390616605453969) : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_89 :
    remainder3Coefficient1.coeff 89 =
      -((3630638964678 * 10 ^ 70 +
        3321494750452325924261132158383094534561620618735540843181656110877606) : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_90 :
    remainder3Coefficient1.coeff 90 =
      ((4182085036846 * 10 ^ 70 +
        6332543540512067269925867952266014135021476035233000503827107453223316) : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_91 :
    remainder3Coefficient1.coeff 91 =
      -((4526827747797 * 10 ^ 70 +
        5586076434411748099016157251310647240396603582270928289374218893435263) : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_92 :
    remainder3Coefficient1.coeff 92 =
      ((4609377669875 * 10 ^ 70 +
        2015643986033340566562149185287772005783886578615378058437004567684813) : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_93 :
    remainder3Coefficient1.coeff 93 =
      -((4418356107718 * 10 ^ 70 +
        8996806071573938147676850018484377312384702936056805188796924819861325) : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_94 :
    remainder3Coefficient1.coeff 94 =
      ((3988907585512 * 10 ^ 70 +
        1581495438948013265896228240917966746911158209976841867902727122876887) : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_95 :
    remainder3Coefficient1.coeff 95 =
      -((3392476858846 * 10 ^ 70 +
        3739760834086536421430287865013236677602261259861102372066072850462997) : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_96 :
    remainder3Coefficient1.coeff 96 =
      ((2717921989088 * 10 ^ 70 +
        5557877643306455097673083855955951862969115128872200019545705566982315) : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_97 :
    remainder3Coefficient1.coeff 97 =
      -((2050650785790 * 10 ^ 70 +
        8575837110185319625117014694537599200934317278556929481254127853562549) : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_98 :
    remainder3Coefficient1.coeff 98 =
      ((1456263400638 * 10 ^ 70 +
        3149416760999611782399304971132695187026094186416292925865657152703900) : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_99 :
    remainder3Coefficient1.coeff 99 =
      -((972537751595 * 10 ^ 70 +
        8751876262428885713982485030724452249106034199225362682938159166413016) : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_100 :
    remainder3Coefficient1.coeff 100 =
      ((610038461958 * 10 ^ 70 +
        8948366820489879908557739215404298729479391143929861637866729604457533) : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_101 :
    remainder3Coefficient1.coeff 101 =
      -((358806945334 * 10 ^ 70 +
        8029601709809758965314778462661253735268111856665578436012941567200002) : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_102 :
    remainder3Coefficient1.coeff 102 =
      ((197437371612 * 10 ^ 70 +
        3957634869376279894372047384264888664388286890466656349383544115360163) : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_103 :
    remainder3Coefficient1.coeff 103 =
      -((101326692384 * 10 ^ 70 +
        6325179505239585369117993025728288204184537341584019354554314103917757) : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_104 :
    remainder3Coefficient1.coeff 104 =
      ((48294572029 * 10 ^ 70 +
        3470433309490047398087627204637894595049763822438025225764127409906729) : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_105 :
    remainder3Coefficient1.coeff 105 =
      -((21248342029 * 10 ^ 70 +
        5296488441844831984739845110213850679632154677322289552445387763338952) : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_106 :
    remainder3Coefficient1.coeff 106 =
      ((8552093080 * 10 ^ 70 +
        0323862608921055837306391440638217718883126650661010452375201449136544) : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_107 :
    remainder3Coefficient1.coeff 107 =
      -((3103121936 * 10 ^ 70 +
        7880682793436916875037180352977051960182882782303518476488465295634159) : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_108 :
    remainder3Coefficient1.coeff 108 =
      ((988616928 * 10 ^ 70 +
        6178010552278236759819134929554734549649775519754451399698435242206457) : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_109 :
    remainder3Coefficient1.coeff 109 =
      -((261015119 * 10 ^ 70 +
        2256878161377874578099475093860301470309729828314733853290122116329096) : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_110 :
    remainder3Coefficient1.coeff 110 =
      ((47541616 * 10 ^ 70 +
        9395747393993690774587995672010918662672232166626647879630890554139506) : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_111 :
    remainder3Coefficient1.coeff 111 =
      ((680725 * 10 ^ 70 +
        8215601181270825551708928620507941647742229886613921890657166990056625) : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_112 :
    remainder3Coefficient1.coeff 112 =
      -((5677349 * 10 ^ 70 +
        2575788127203591776336052068471315035546375162400502978977957918879915) : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_113 :
    remainder3Coefficient1.coeff 113 =
      ((3264142 * 10 ^ 70 +
        2498515100281541262273026639951336885094860458705571347218406782191670) : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_114 :
    remainder3Coefficient1.coeff 114 =
      -((1296197 * 10 ^ 70 +
        4768585141306529739412325910605254911809266707173444777754199197117405) : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_115 :
    remainder3Coefficient1.coeff 115 =
      ((411210 * 10 ^ 70 +
        0615905650925761907793181318489600313256560203059785385739302444440528) : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_116 :
    remainder3Coefficient1.coeff 116 =
      -((106943 * 10 ^ 70 +
        8292863121591341343098989279807575505500494470269216423749908517787097) : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_117 :
    remainder3Coefficient1.coeff 117 =
      ((22131 * 10 ^ 70 +
        6659772670166692895082049494369426799689678856502350466588757680944315) : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_118 :
    remainder3Coefficient1.coeff 118 =
      -((3161 * 10 ^ 70 +
        2871547811751919971175442334048754532200354187620055162056546536666592) : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_119 :
    remainder3Coefficient1.coeff 119 =
      ((61 * 10 ^ 70 +
        1752879729334922764789269955569477349949902997553095919933524614039751) : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_120 :
    remainder3Coefficient1.coeff 120 =
      ((145 * 10 ^ 70 +
        4576979830563366719294775279603741617520000804671943305892791271946524) : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_121 :
    remainder3Coefficient1.coeff 121 =
      -((60 * 10 ^ 70 +
        1983510415873099185742587321856897532228258987522196529103207795599249) : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_122 :
    remainder3Coefficient1.coeff 122 =
      ((16 * 10 ^ 70 +
        0673108225330972831596641133967268423928982157302465845839001602843914) : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_123 :
    remainder3Coefficient1.coeff 123 =
      -((3 * 10 ^ 70 +
        3159189961298257144236198994417581469091854311710197435272783921001811) : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_124 :
    remainder3Coefficient1.coeff 124 =
      (5500690565123684648068027453042753689649826253269721262388770496426180 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_125 :
    remainder3Coefficient1.coeff 125 =
      (-727320140970134352554732927035915214612111696900761659515242968612036 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_126 :
    remainder3Coefficient1.coeff 126 =
      (72187319352308426801146532368161192757279536276969014179403904369732 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_127 :
    remainder3Coefficient1.coeff 127 =
      (-4218244686005705265308018284230687237289489357001229744584333300507 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_128 :
    remainder3Coefficient1.coeff 128 =
      (-139307632926777985198982076496959313080569609220227305142667906283 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_129 :
    remainder3Coefficient1.coeff 129 =
      (74195559968049977844094353834252111881072072129491686892782427928 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_130 :
    remainder3Coefficient1.coeff 130 =
      (-11000878240301108446232847583891856362587171660360346433747772014 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_131 :
    remainder3Coefficient1.coeff 131 =
      (1071177102373187841768649437842988267533738719301055727435847552 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_132 :
    remainder3Coefficient1.coeff 132 =
      (-75779327597226316549893017568008428679137405770638801204431961 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_133 :
    remainder3Coefficient1.coeff 133 =
      (3941362457426846987591807964942227553872051291430027126569177 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_134 :
    remainder3Coefficient1.coeff 134 =
      (-147335209057738889554839018861819964914468200136625830998411 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_135 :
    remainder3Coefficient1.coeff 135 =
      (3765636401631912124103489222329610653087092710226271636432 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_136 :
    remainder3Coefficient1.coeff 136 =
      (-60176317700103030329492405261393362787408546349180388892 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_137 :
    remainder3Coefficient1.coeff 137 =
      (494637248126954007030269825502921126464763316763120633 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_138 :
    remainder3Coefficient1.coeff 138 =
      (-585404634050633860856164267033391374720611073085002 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_139 :
    remainder3Coefficient1.coeff 139 =
      (-18075531155479761994337968259563696552934565603073 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_140 :
    remainder3Coefficient1.coeff 140 =
      (88688412798114701400044474593236585742109067413 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_141 :
    remainder3Coefficient1.coeff 141 =
      (33286756372807294838081351857126589748431361 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_142 :
    remainder3Coefficient1.coeff 142 =
      (-947983312731369225699789814629797199677964 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_143 :
    remainder3Coefficient1.coeff 143 =
      (2020920246644392060969107822451951528536 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_144 :
    remainder3Coefficient1.coeff 144 =
      (-1592238664499157879719509935713969035 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_145 :
    remainder3Coefficient1.coeff 145 =
      (454584863828938384243537124772738 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_146 :
    remainder3Coefficient1.coeff 146 =
      (-38542448209451443600274287315 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_147 :
    remainder3Coefficient1.coeff 147 =
      (702479133103523993168864 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_148 :
    remainder3Coefficient1.coeff 148 =
      (-1620196522930594940 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_149 :
    remainder3Coefficient1.coeff 149 =
      (140328271398 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_150 :
    remainder3Coefficient1.coeff 150 =
      (-71 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
