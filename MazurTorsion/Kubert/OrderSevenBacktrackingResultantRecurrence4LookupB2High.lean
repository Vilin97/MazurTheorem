/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData4
import Mathlib.Tactic.NormNum

/-!
# Recurrence 4 lookup certificate: B2 source coefficients, high half

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence4B2_coeff_85 :
    remainder5Coefficient2.coeff 85 =
      ((1474095467598168624371197998419163 * 10 ^ 70 +
        8101459131632143218445668194720032948591883024153709295719308467965307) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_86 :
    remainder5Coefficient2.coeff 86 =
      ((363696904451306511356089697371203 * 10 ^ 70 +
        8893263543764066605453245825932418430889471703920340704574925883183841) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_87 :
    remainder5Coefficient2.coeff 87 =
      -((1626373199221243266992636758085879 * 10 ^ 70 +
        9412567806053139804217998010454074377006014775975685360643030088177756) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_88 :
    remainder5Coefficient2.coeff 88 =
      ((2316407967377042986099057938555278 * 10 ^ 70 +
        8956737947325901181834041145384964611683939868403400302344480035722497) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_89 :
    remainder5Coefficient2.coeff 89 =
      -((2519712351796641313410057683843612 * 10 ^ 70 +
        3978148486708585798969801255126223690468821464850733139521027463025036) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_90 :
    remainder5Coefficient2.coeff 90 =
      ((2370125498815781343547470153591894 * 10 ^ 70 +
        6261564750990371941059258137390837019493768022561133635688133087569277) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_91 :
    remainder5Coefficient2.coeff 91 =
      -((2012335081085046106579863841785737 * 10 ^ 70 +
        0806758000230965031363012405897823480331187818763233278574076052069703) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_92 :
    remainder5Coefficient2.coeff 92 =
      ((1572754177225461532009576839560150 * 10 ^ 70 +
        8995357668441210822957786597908959969020861966761461112421149470169567) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_93 :
    remainder5Coefficient2.coeff 93 =
      -((1143180091711424600952238530738522 * 10 ^ 70 +
        4606514949502972405835280943988480749635908088326677401925142426072745) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_94 :
    remainder5Coefficient2.coeff 94 =
      ((777155344391878481579733269848735 * 10 ^ 70 +
        4465202776085475718338082138731401713552187031791586947790132739722068) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_95 :
    remainder5Coefficient2.coeff 95 =
      -((495546927731602255476325552126354 * 10 ^ 70 +
        8618001059195115732939171597108586154042994104094913112677329953201008) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_96 :
    remainder5Coefficient2.coeff 96 =
      ((296618430108367947126579842065804 * 10 ^ 70 +
        0168067869479623843000337982714639447106002472539339138500659250099369) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_97 :
    remainder5Coefficient2.coeff 97 =
      -((166464932013983416175282893161600 * 10 ^ 70 +
        6981954377469619451208058949698484722156476394400588505441566922614291) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_98 :
    remainder5Coefficient2.coeff 98 =
      ((87250223856283326598870480925635 * 10 ^ 70 +
        9185933402770935311742876398163750065013303431743918437652678905428353) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_99 :
    remainder5Coefficient2.coeff 99 =
      -((42349421955016473642029398980592 * 10 ^ 70 +
        3294150750619130524143275328875388637352749562650662200364897216435656) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_100 :
    remainder5Coefficient2.coeff 100 =
      ((18695862243618116210955064175471 * 10 ^ 70 +
        2161797198305660785505739198024181006897379562721856127305178082009299) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_101 :
    remainder5Coefficient2.coeff 101 =
      -((7194447033677192922450385992189 * 10 ^ 70 +
        8844617631504662268603616192464514444739519840039858373934730203910107) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_102 :
    remainder5Coefficient2.coeff 102 =
      ((2115609850463252639810528148674 * 10 ^ 70 +
        9402651304107714841840240069271001054861052916537322717453627436840201) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_103 :
    remainder5Coefficient2.coeff 103 =
      -((158346588561602994907969706892 * 10 ^ 70 +
        5381354754360726485218560891009033249552510973109693205727267005404507) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_104 :
    remainder5Coefficient2.coeff 104 =
      -((423378706742964047993482320985 * 10 ^ 70 +
        1364470329617729814709390733305101266704485241533626803476788898037051) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_105 :
    remainder5Coefficient2.coeff 105 =
      ((475534925460099957248227297925 * 10 ^ 70 +
        2666521793768345684397908447580247388717936259715507916303682676215766) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_106 :
    remainder5Coefficient2.coeff 106 =
      -((369159406539023586788895474477 * 10 ^ 70 +
        8080109541189212484295110158372847982648826878027104390340104201984104) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_107 :
    remainder5Coefficient2.coeff 107 =
      ((246639363071765306409015639477 * 10 ^ 70 +
        2571915890260577358487571754389706249585709040630861321025946477398691) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_108 :
    remainder5Coefficient2.coeff 108 =
      -((150817359407829168399691212167 * 10 ^ 70 +
        5351564971286676754851622843582922362827244145562742755509702058293987) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_109 :
    remainder5Coefficient2.coeff 109 =
      ((86523176101395987449367927118 * 10 ^ 70 +
        9510288418881594094112677143321086115654261318869977563225949479982147) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_110 :
    remainder5Coefficient2.coeff 110 =
      -((47092870243874239030244377255 * 10 ^ 70 +
        1830809281210588113817501520045299127878878388904002241539187187495764) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_111 :
    remainder5Coefficient2.coeff 111 =
      ((24437726989759551267027819536 * 10 ^ 70 +
        6265828356474221913256440201756996413157135702369059272742500919850200) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_112 :
    remainder5Coefficient2.coeff 112 =
      -((12111577664486000729336827914 * 10 ^ 70 +
        6199429100716545362484169567696532403162591516112729892625395542267271) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_113 :
    remainder5Coefficient2.coeff 113 =
      ((5732716945617624372140294478 * 10 ^ 70 +
        3793108358931587687345943955204512358856237992135710554411609123821373) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_114 :
    remainder5Coefficient2.coeff 114 =
      -((2588595275295295777988882187 * 10 ^ 70 +
        8929578572359311123936202113615369440981623790523739933762201456830594) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_115 :
    remainder5Coefficient2.coeff 115 =
      ((1113020306216627711888528344 * 10 ^ 70 +
        2436225921328841870487267482012074404879230385898144512400273830314648) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_116 :
    remainder5Coefficient2.coeff 116 =
      -((454518894102923361426702945 * 10 ^ 70 +
        1335912647350311329901963652979436046763693058364427125583840224263669) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_117 :
    remainder5Coefficient2.coeff 117 =
      ((175667060578418913297776379 * 10 ^ 70 +
        2959838460384146968924689804377333055830330134912164437639605822979185) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_118 :
    remainder5Coefficient2.coeff 118 =
      -((63946020702507414413137352 * 10 ^ 70 +
        8270970432519642867774458550296943535567416313721229052678225285663489) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_119 :
    remainder5Coefficient2.coeff 119 =
      ((21770246762987466370142511 * 10 ^ 70 +
        3797425334609378118884877042652535622188195808770239794492489912610349) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_120 :
    remainder5Coefficient2.coeff 120 =
      -((6856455511348634303560625 * 10 ^ 70 +
        0804641556598105440603976420869450858016779442366478348176142667408153) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_121 :
    remainder5Coefficient2.coeff 121 =
      ((1961181562986678885161085 * 10 ^ 70 +
        0733548996570223430553322596433687735942001743896916758442989295198224) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_122 :
    remainder5Coefficient2.coeff 122 =
      -((491789095038424468185697 * 10 ^ 70 +
        6902907539687838095555857624496693297751579789386737933808519868701785) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_123 :
    remainder5Coefficient2.coeff 123 =
      ((99369375798599882498824 * 10 ^ 70 +
        5978843032728333671207324348266178876871608427051119186911484265614266) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_124 :
    remainder5Coefficient2.coeff 124 =
      -((11553744334825640008932 * 10 ^ 70 +
        2037535826236670322885522334047046792237898235696506329710224248808763) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_125 :
    remainder5Coefficient2.coeff 125 =
      -((2099730842079096586981 * 10 ^ 70 +
        4615532819771546303289388152839168412315897914927384953449667053529622) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_126 :
    remainder5Coefficient2.coeff 126 =
      ((1936597598894396929234 * 10 ^ 70 +
        8860982179527704173490972806030509008699183796703371413784266338955636) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_127 :
    remainder5Coefficient2.coeff 127 =
      -((767180486179142068241 * 10 ^ 70 +
        3935290822701167643975612370831282710607106439879108904397587291341207) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_128 :
    remainder5Coefficient2.coeff 128 =
      ((218063804020651361616 * 10 ^ 70 +
        7136984288897456462146535337537095846584709967677972471196971129235279) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_129 :
    remainder5Coefficient2.coeff 129 =
      -((50237798951839081284 * 10 ^ 70 +
        4156840858217174562998126517221041762453089716623633020228721460933898) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_130 :
    remainder5Coefficient2.coeff 130 =
      ((12556212431066953055 * 10 ^ 70 +
        7762639381015351733722867607778211579772720121438246048520585398512707) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_131 :
    remainder5Coefficient2.coeff 131 =
      -((5363336961436103422 * 10 ^ 70 +
        2496964875953946973042786574916545240873780813063083104541880995619499) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_132 :
    remainder5Coefficient2.coeff 132 =
      ((3001567109286617510 * 10 ^ 70 +
        2002681250514275827854856885767459727840804046446143580701334084527894) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_133 :
    remainder5Coefficient2.coeff 133 =
      -((1509713909041288323 * 10 ^ 70 +
        2947355121747480875807004646049343118687469650402056252259591938855170) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_134 :
    remainder5Coefficient2.coeff 134 =
      ((649682071700628293 * 10 ^ 70 +
        3269048075191588681764646785841490468827118951733426077221600868755095) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_135 :
    remainder5Coefficient2.coeff 135 =
      -((256965970893395720 * 10 ^ 70 +
        2015256765463304206182926192126311067516391667855332512623393449143986) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_136 :
    remainder5Coefficient2.coeff 136 =
      ((103465175915625107 * 10 ^ 70 +
        4196850700238277949594443141524409287363249184479582505979611600846920) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_137 :
    remainder5Coefficient2.coeff 137 =
      -((44564335429059325 * 10 ^ 70 +
        9667777434071434981400163917839975468859228394964881233764317405886620) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_138 :
    remainder5Coefficient2.coeff 138 =
      ((19611446619436349 * 10 ^ 70 +
        7914835912801563137082536041700410449133576850279636450699407002644828) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_139 :
    remainder5Coefficient2.coeff 139 =
      -((8189277452076996 * 10 ^ 70 +
        3679436620941142757370007389201575217659680752301560088009221326107095) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_140 :
    remainder5Coefficient2.coeff 140 =
      ((3106013847250116 * 10 ^ 70 +
        0025571083285897623731687718569606062123980344678784600759712934397504) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_141 :
    remainder5Coefficient2.coeff 141 =
      -((1054916364784178 * 10 ^ 70 +
        9520993027938846280469369389105991870879379202198782160338822532555371) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_142 :
    remainder5Coefficient2.coeff 142 =
      ((320565183917474 * 10 ^ 70 +
        4399038169798964066675373925123456761736139710408785532363116629765235) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_143 :
    remainder5Coefficient2.coeff 143 =
      -((87238073176953 * 10 ^ 70 +
        2474784613595405492817870399402846062373146770936797864863153841708192) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_144 :
    remainder5Coefficient2.coeff 144 =
      ((21182349888031 * 10 ^ 70 +
        5682869082180732391060738139848088450706087313057948924660455540352359) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_145 :
    remainder5Coefficient2.coeff 145 =
      -((4535871973200 * 10 ^ 70 +
        2874131274821081748412282593376026654419783383077665127041227179401237) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_146 :
    remainder5Coefficient2.coeff 146 =
      ((838140793860 * 10 ^ 70 +
        2836608465013211428362771883520036432590861852695991863643476156134706) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_147 :
    remainder5Coefficient2.coeff 147 =
      -((128771123797 * 10 ^ 70 +
        2584129388393433221789307451845623210726342426623178197500075316364922) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_148 :
    remainder5Coefficient2.coeff 148 =
      ((15281121294 * 10 ^ 70 +
        1378562748978438240808132058529940293936109133201187086084410814795117) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_149 :
    remainder5Coefficient2.coeff 149 =
      -((1114747639 * 10 ^ 70 +
        7470838399173845866963537556101058965969221212489308536981589065294677) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_150 :
    remainder5Coefficient2.coeff 150 =
      -((27462086 * 10 ^ 70 +
        2137779537866446421403435941821743509743349305503717766544547627206804) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_151 :
    remainder5Coefficient2.coeff 151 =
      ((23690192 * 10 ^ 70 +
        4512963338066951312034159925146237684426376803756898817191434628405017) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_152 :
    remainder5Coefficient2.coeff 152 =
      -((4144834 * 10 ^ 70 +
        0183650072190631687868324479652150897921353001831497614064354914375869) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_153 :
    remainder5Coefficient2.coeff 153 =
      ((447303 * 10 ^ 70 +
        2281840300991362387649452378332904851754603927993511137708532981198646) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_154 :
    remainder5Coefficient2.coeff 154 =
      -((32124 * 10 ^ 70 +
        9402499620072347858002134140887636842805706637889786069297935845292425) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_155 :
    remainder5Coefficient2.coeff 155 =
      ((1452 * 10 ^ 70 +
        7783499082520375057857754162668424168881483138790498073831631580080663) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_156 :
    remainder5Coefficient2.coeff 156 =
      -((34 * 10 ^ 70 +
        7088711886250970692293235833210607372947626484060918639373937496992839) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_157 :
    remainder5Coefficient2.coeff 157 =
      (2510292902318978053831865535295045378849514342696839859168512863197032 : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_158 :
    remainder5Coefficient2.coeff 158 =
      (11879479230306445822615858779914807894582012806926966857560387964525 : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_159 :
    remainder5Coefficient2.coeff 159 =
      (-104312178269444762808743017017193547254177946724576725993741185135 : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_160 :
    remainder5Coefficient2.coeff 160 =
      (-35293309092693130193092614851777430488740861861679988156283197 : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_161 :
    remainder5Coefficient2.coeff 161 =
      (901990492351639645394371220901405226935166387424071994660786 : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_162 :
    remainder5Coefficient2.coeff 162 =
      (-1374558268844116244828640071139234830452149625881717600077 : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_163 :
    remainder5Coefficient2.coeff 163 =
      (606230329235390967552843126457705192146625266405369913 : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_164 :
    remainder5Coefficient2.coeff 164 =
      (-72519115701450106230107972658119229527810025982051 : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_165 :
    remainder5Coefficient2.coeff 165 =
      (1936443151073259926394357518664301167601012831 : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_166 :
    remainder5Coefficient2.coeff 166 =
      (-8483347705126631367621564019868229046546 : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_167 :
    remainder5Coefficient2.coeff 167 =
      (3661122349119735226781204871536038 : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_168 :
    remainder5Coefficient2.coeff 168 =
      (-56736521273791373632394593 : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
