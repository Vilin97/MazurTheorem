/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData2
import Mathlib.Tactic.NormNum

/-!
# Recurrence 2 lookup certificate: C0 source coefficients, high half

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence2C0_coeff_98 :
    remainder4Coefficient0.coeff 98 =
      ((12662604029483479757195248051429 * 10 ^ 70 +
        2180009587081760533165610098963522774357757065017484508971799156382836) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_99 :
    remainder4Coefficient0.coeff 99 =
      -((12632148482534420193536655608232 * 10 ^ 70 +
        6148735100196612474026939368204357909253178140160758936454815644166696) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_100 :
    remainder4Coefficient0.coeff 100 =
      ((12230126503601930341531452801230 * 10 ^ 70 +
        4907393025986429557483066527253106630883182523782152055356014364325738) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_101 :
    remainder4Coefficient0.coeff 101 =
      -((11495563806837846253007446464285 * 10 ^ 70 +
        9908237737801388516615475027501476851818983893644236746873240044281827) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_102 :
    remainder4Coefficient0.coeff 102 =
      ((10493526471039670206565701912836 * 10 ^ 70 +
        3206581172654491977992962981300636989593654077415105199601658010018037) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_103 :
    remainder4Coefficient0.coeff 103 =
      -((9305654995741843011486379733974 * 10 ^ 70 +
        2466549319657923719821590313925592279407849583250057840444537701689525) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_104 :
    remainder4Coefficient0.coeff 104 =
      ((8019374579993495546092908358739 * 10 ^ 70 +
        6213766088863321819627230907331641852778063353176704322117091952393838) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_105 :
    remainder4Coefficient0.coeff 105 =
      -((6717716837624141703740563540663 * 10 ^ 70 +
        7009835423428541809074248361209103000730135920219318270762023196963841) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_106 :
    remainder4Coefficient0.coeff 106 =
      ((5471293281582856614101615982839 * 10 ^ 70 +
        7660686624970568832893382254160742719901660530258973068987360397800664) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_107 :
    remainder4Coefficient0.coeff 107 =
      -((4333300911435324100510622347716 * 10 ^ 70 +
        9006285099269362645699371981190478917957817576353834422942697688414949) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_108 :
    remainder4Coefficient0.coeff 108 =
      ((3337722509207044125978682844943 * 10 ^ 70 +
        6888088146998009550775937263797688852956198465792959932334606410340605) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_109 :
    remainder4Coefficient0.coeff 109 =
      -((2500288624320017241248628512307 * 10 ^ 70 +
        7333040066900144193559513134335415011920789386673805526194072509470971) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_110 :
    remainder4Coefficient0.coeff 110 =
      ((1821400921560176799412849637655 * 10 ^ 70 +
        4248134440622365374814229327520036047042332052019722107045243251748107) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_111 :
    remainder4Coefficient0.coeff 111 =
      -((1290098797641827245511677042636 * 10 ^ 70 +
        1117259237589694742558650146762244516615780377440442632468301836509693) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_112 :
    remainder4Coefficient0.coeff 112 =
      ((888237308756652257076169893393 * 10 ^ 70 +
        1998564198884533227143845133678795769295569834266830431762401028405012) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_113 :
    remainder4Coefficient0.coeff 113 =
      -((594254865299328145856774634785 * 10 ^ 70 +
        2255136537423787501429144906382914636755851784277345405858704500248988) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_114 :
    remainder4Coefficient0.coeff 114 =
      ((386162167414565511039597145135 * 10 ^ 70 +
        8927048912926417243294689358176233525448625139119174233523511264696948) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_115 :
    remainder4Coefficient0.coeff 115 =
      -((243616817395785654293355366889 * 10 ^ 70 +
        0569449587307747636021921105236983100534372388041396308390473458905844) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_116 :
    remainder4Coefficient0.coeff 116 =
      ((149125063373972638456726829127 * 10 ^ 70 +
        0075882600450616815235209148286537305636532802475313193501966740361357) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_117 :
    remainder4Coefficient0.coeff 117 =
      -((88521693551638962344433609686 * 10 ^ 70 +
        5658420195959387878825044945900972219761050604641867818095167097415767) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_118 :
    remainder4Coefficient0.coeff 118 =
      ((50926725241697205679038206318 * 10 ^ 70 +
        1109735462791639457453461198421574353339340863613119796821972197776385) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_119 :
    remainder4Coefficient0.coeff 119 =
      -((28377767018573920800728208444 * 10 ^ 70 +
        4411767286395976604516072586918306535338214559109218648594455052823570) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_120 :
    remainder4Coefficient0.coeff 120 =
      ((15307050905468875091689382938 * 10 ^ 70 +
        8517833970706280802032143818843438745772413605297262732057065643004876) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_121 :
    remainder4Coefficient0.coeff 121 =
      -((7988067482521468214447588041 * 10 ^ 70 +
        5021401559061301876770854651563396310945684215254224789233995147201916) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_122 :
    remainder4Coefficient0.coeff 122 =
      ((4030910409351765866568855177 * 10 ^ 70 +
        4002702699996601610905479054242087687966505088654551009611193854506956) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_123 :
    remainder4Coefficient0.coeff 123 =
      -((1965959803442018964242243123 * 10 ^ 70 +
        7518250458131436693718989939518336017115117182576367161321289862539042) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_124 :
    remainder4Coefficient0.coeff 124 =
      ((926369873267232628347995011 * 10 ^ 70 +
        9063956543496492515726203072200778978532344750130083074292290492617528) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_125 :
    remainder4Coefficient0.coeff 125 =
      -((421591279968884999075981042 * 10 ^ 70 +
        3574630129915741252372484670899997963862324261798153052452984602912208) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_126 :
    remainder4Coefficient0.coeff 126 =
      ((185259622283411307861515761 * 10 ^ 70 +
        4276997510506997085284286083259069147730550769855520321525719001923194) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_127 :
    remainder4Coefficient0.coeff 127 =
      -((78585826526001038936607656 * 10 ^ 70 +
        9384857276472626283626358731911234352063969411485792704621660776776354) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_128 :
    remainder4Coefficient0.coeff 128 =
      ((32169581093595491238347410 * 10 ^ 70 +
        5457065748459244161943360879419341203113287467726101807530815010869209) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_129 :
    remainder4Coefficient0.coeff 129 =
      -((12701532305580758981869393 * 10 ^ 70 +
        9983861809005141790222295341517889348189439411915412935684901186703249) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_130 :
    remainder4Coefficient0.coeff 130 =
      ((4832407485142669103604109 * 10 ^ 70 +
        4721842852474137295827183509955857824460899585581078019896944505665114) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_131 :
    remainder4Coefficient0.coeff 131 =
      -((1768686219770742383612894 * 10 ^ 70 +
        8229003143792222106171519931896192825804973477202712212640706043473210) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_132 :
    remainder4Coefficient0.coeff 132 =
      ((621114531918855517631801 * 10 ^ 70 +
        8717277488710337064758040279934454229239953558466606442510120418980142) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_133 :
    remainder4Coefficient0.coeff 133 =
      -((208486816178194828335375 * 10 ^ 70 +
        1867957221253412805803519634062942669876278621148888472516713577948315) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_134 :
    remainder4Coefficient0.coeff 134 =
      ((66582855886621409456102 * 10 ^ 70 +
        3655397455171852542239374068652319004731304805759406940300851074927160) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_135 :
    remainder4Coefficient0.coeff 135 =
      -((20159260850093237946271 * 10 ^ 70 +
        7923808634549548301395976506419878063048853253855941199215641267367734) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_136 :
    remainder4Coefficient0.coeff 136 =
      ((5811057359225377074159 * 10 ^ 70 +
        2308783698209844404775846232880797963742703507883672587042853145083240) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_137 :
    remainder4Coefficient0.coeff 137 =
      -((1646781746325023378546 * 10 ^ 70 +
        3002771692627547415566507959451894040923261544260465977194023645689406) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_138 :
    remainder4Coefficient0.coeff 138 =
      ((506767745695882665649 * 10 ^ 70 +
        4802377291967996322488940339032824922973525105513771493673889786327703) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_139 :
    remainder4Coefficient0.coeff 139 =
      -((197946152086317438183 * 10 ^ 70 +
        8963682910249173038027472331925446763620985973139180598096838704353132) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_140 :
    remainder4Coefficient0.coeff 140 =
      ((101242643784047159708 * 10 ^ 70 +
        7639851903285467950777554264908212689932507934270083873145824625390286) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_141 :
    remainder4Coefficient0.coeff 141 =
      -((58711666528865418899 * 10 ^ 70 +
        0084485370387462315861002146253164023248959322499495099409498451605896) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_142 :
    remainder4Coefficient0.coeff 142 =
      ((34074759913310788545 * 10 ^ 70 +
        3681430593449313176893901264438370580639581632036713276967762101034757) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_143 :
    remainder4Coefficient0.coeff 143 =
      -((18836755067944890009 * 10 ^ 70 +
        2307650178385255172990306481893427253590432990430689415464963467522189) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_144 :
    remainder4Coefficient0.coeff 144 =
      ((9789817918703860593 * 10 ^ 70 +
        2460234275820622197149787784046631454571167813448784816051813439014143) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_145 :
    remainder4Coefficient0.coeff 145 =
      -((4771656339941745681 * 10 ^ 70 +
        5817923802835406294553144121332619012770916698889854590375114699627608) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
