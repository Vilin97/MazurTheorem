/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData4
import Mathlib.Tactic.NormNum

/-!
# Recurrence 4 lookup certificate: A3 source coefficients, high half

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence4A3_coeff_92 :
    remainder4Coefficient3.coeff 92 =
      ((176473385274789241837392718516 * 10 ^ 70 +
        0982747015888460662198709227079720842388611628989672141453076644495590) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_93 :
    remainder4Coefficient3.coeff 93 =
      -((184267523154347832662993382789 * 10 ^ 70 +
        2331600543518685231226110809092316041540282752680344181264185937438711) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_94 :
    remainder4Coefficient3.coeff 94 =
      ((185947126009607934978739452010 * 10 ^ 70 +
        4925149782700238059717281009253639961586281559191142076347303417279029) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_95 :
    remainder4Coefficient3.coeff 95 =
      -((181338781754327948328037886149 * 10 ^ 70 +
        5910969449061829548911610912009345890801384750740394232244220790305342) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_96 :
    remainder4Coefficient3.coeff 96 =
      ((170898026186980064134473531030 * 10 ^ 70 +
        8792652215120492987053762497236748463473918861393220405508017747355876) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_97 :
    remainder4Coefficient3.coeff 97 =
      -((155635345667211120426214160261 * 10 ^ 70 +
        2810881101969296649776030742297880857785399860292294493559867890291365) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_98 :
    remainder4Coefficient3.coeff 98 =
      ((136955377753757312870694983358 * 10 ^ 70 +
        3184668269630637911157150809910172656821222705971535041015937089604267) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_99 :
    remainder4Coefficient3.coeff 99 =
      -((116444656727476734612279126401 * 10 ^ 70 +
        7339854213209270800270590025416037055438399201236525558883619271536937) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_100 :
    remainder4Coefficient3.coeff 100 =
      ((95652144093327838293790355899 * 10 ^ 70 +
        9401742732288687997964431433478088083255333089172882998097381524861447) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_101 :
    remainder4Coefficient3.coeff 101 =
      -((75903996333230026382439846932 * 10 ^ 70 +
        7722766929827925629698390945089800158299573819753617593331621322067580) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_102 :
    remainder4Coefficient3.coeff 102 =
      ((58181445440687775046921112637 * 10 ^ 70 +
        2312228514222012036448111881122888356968009096274469224877111716449663) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_103 :
    remainder4Coefficient3.coeff 103 =
      -((43072930026168003558941124228 * 10 ^ 70 +
        2572521572083738592604777143108468777170791672659615118559872265113791) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_104 :
    remainder4Coefficient3.coeff 104 =
      ((30794232145005058207521234329 * 10 ^ 70 +
        5023654388748488025754663300088680602785710391526345509263212383916376) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_105 :
    remainder4Coefficient3.coeff 105 =
      -((21257844054666340032918890399 * 10 ^ 70 +
        6651951419112378465454427532977997962162412668300190128561804392002306) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_106 :
    remainder4Coefficient3.coeff 106 =
      ((14167344151357462258553470309 * 10 ^ 70 +
        0362545497692308724895744414032736416193683922164774746612234423585873) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_107 :
    remainder4Coefficient3.coeff 107 =
      -((9113939393630718930392049703 * 10 ^ 70 +
        8853651992130687155879859103889800506596345445567843981944630977269690) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_108 :
    remainder4Coefficient3.coeff 108 =
      ((5658427511013853518622954762 * 10 ^ 70 +
        6211089361166854968938163810626406852108212249596016989233906078892612) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_109 :
    remainder4Coefficient3.coeff 109 =
      -((3389806746333968469680039414 * 10 ^ 70 +
        6573658019918964381953355396073497953039215996244393540520294236026118) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_110 :
    remainder4Coefficient3.coeff 110 =
      ((1959093798977341411901076074 * 10 ^ 70 +
        8535189002444420553780638678155087392621845336597690492881284736605936) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_111 :
    remainder4Coefficient3.coeff 111 =
      -((1092048120510662783206136156 * 10 ^ 70 +
        0676051511299682632899560986633923169809086424964405012638370227444059) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_112 :
    remainder4Coefficient3.coeff 112 =
      ((586993116935681584840736220 * 10 ^ 70 +
        1919350713865214816830779311659945179831847552187491410601345271337213) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_113 :
    remainder4Coefficient3.coeff 113 =
      -((304172808945607598683979734 * 10 ^ 70 +
        4499612882974177869325658837674013608837094572823587644737759559765755) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_114 :
    remainder4Coefficient3.coeff 114 =
      ((151910704842196142209882497 * 10 ^ 70 +
        2382999243094599440090491518910907156231194781116445432241807824877411) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_115 :
    remainder4Coefficient3.coeff 115 =
      -((73099595631230280325206112 * 10 ^ 70 +
        0070793112430484702325413531155248649221727297149062161532066504098032) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_116 :
    remainder4Coefficient3.coeff 116 =
      ((33882332954984642778561477 * 10 ^ 70 +
        3820804768531740287711515571794132771153365533156929607882417314586377) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_117 :
    remainder4Coefficient3.coeff 117 =
      -((15122902149330239841165866 * 10 ^ 70 +
        8128075030377744965170374800242649512606742882149195720968994942824104) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_118 :
    remainder4Coefficient3.coeff 118 =
      ((6497966021375530904313245 * 10 ^ 70 +
        0240672650550574707536452882422460639368321470950190129782641237496299) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_119 :
    remainder4Coefficient3.coeff 119 =
      -((2687158721072196903153304 * 10 ^ 70 +
        9479749620208473971994248542300021158436520054416376118405511770926595) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_120 :
    remainder4Coefficient3.coeff 120 =
      ((1069323165678915503923484 * 10 ^ 70 +
        4433052426485068593826311228692474359229677832366040167901603216952640) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_121 :
    remainder4Coefficient3.coeff 121 =
      -((409455984444779808541789 * 10 ^ 70 +
        6418157018161753409951353504760407600758844774528077630862364817336807) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_122 :
    remainder4Coefficient3.coeff 122 =
      ((150888783553353839422656 * 10 ^ 70 +
        8910256446539785832756053507015439620520167418111593329581571679804254) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_123 :
    remainder4Coefficient3.coeff 123 =
      -((53535801485746155776805 * 10 ^ 70 +
        6057287935963117902385157780063985583237170594353294546161083630999250) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_124 :
    remainder4Coefficient3.coeff 124 =
      ((18301924947629422074174 * 10 ^ 70 +
        1632701538664775820651064420965680916344169757483868125902687615200995) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_125 :
    remainder4Coefficient3.coeff 125 =
      -((6035156688308510334621 * 10 ^ 70 +
        5231974900826773200124788015357824866192640621217557378321203959237944) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_126 :
    remainder4Coefficient3.coeff 126 =
      ((1922312304256268430934 * 10 ^ 70 +
        6707626267801966647489410462750256418131824989131787276890961981606037) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_127 :
    remainder4Coefficient3.coeff 127 =
      -((592433276435154301038 * 10 ^ 70 +
        7521575441256690901149228082702865388144409126844516721348939257884575) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_128 :
    remainder4Coefficient3.coeff 128 =
      ((177088607875047042091 * 10 ^ 70 +
        3230365089098629244038125760830735646836165103879779377413046979699671) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_129 :
    remainder4Coefficient3.coeff 129 =
      -((51601590765205889665 * 10 ^ 70 +
        9858643047069216575905817170663286377494951100705815133031414267194503) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_130 :
    remainder4Coefficient3.coeff 130 =
      ((14847912830643731742 * 10 ^ 70 +
        0743031372173481168651497569495291661894331894880277431155781563674464) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_131 :
    remainder4Coefficient3.coeff 131 =
      -((4352603552699508176 * 10 ^ 70 +
        2495129050860873617178192092238007707779865793963810213773283153669119) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_132 :
    remainder4Coefficient3.coeff 132 =
      ((1377244768107497777 * 10 ^ 70 +
        5482122965522486228107777662161008626716679042899544292659136422439732) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_133 :
    remainder4Coefficient3.coeff 133 =
      -((499658828023131603 * 10 ^ 70 +
        2799825365138056246341966657455872235270255274996065298133171773154231) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_134 :
    remainder4Coefficient3.coeff 134 =
      ((207699603250264637 * 10 ^ 70 +
        1256759509479349899292290388645248952637575887906350900379018312867083) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_135 :
    remainder4Coefficient3.coeff 135 =
      -((91769796553905303 * 10 ^ 70 +
        4632507067092885548139982510666664888556477412820073992851635974699773) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_136 :
    remainder4Coefficient3.coeff 136 =
      ((39332485312782678 * 10 ^ 70 +
        3998681280819662608407261846836122289706157624998779732763792086090013) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_137 :
    remainder4Coefficient3.coeff 137 =
      -((15092430299684798 * 10 ^ 70 +
        3685576211103818442186411079410809830514442796940887379675877414460350) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_138 :
    remainder4Coefficient3.coeff 138 =
      ((4657208485277643 * 10 ^ 70 +
        2778679041473559912311693920611412708553328658175144501928284214097193) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_139 :
    remainder4Coefficient3.coeff 139 =
      -((788272057103497 * 10 ^ 70 +
        9905284501067927947459849182118137209658298636041716758126560186773715) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_140 :
    remainder4Coefficient3.coeff 140 =
      -((289389134448183 * 10 ^ 70 +
        0234482396875656949386206366238490122630698334674495904732983104655864) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_141 :
    remainder4Coefficient3.coeff 141 =
      ((387458105070408 * 10 ^ 70 +
        7290217259661452022661790646466103340836328273420206027089601394339523) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_142 :
    remainder4Coefficient3.coeff 142 =
      -((252740290434241 * 10 ^ 70 +
        0222873814658861301648844020209383938468991764041686548768398572197537) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_143 :
    remainder4Coefficient3.coeff 143 =
      ((126865679732660 * 10 ^ 70 +
        2073819349766682631278235671165446753619285485969410050283032391681739) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_144 :
    remainder4Coefficient3.coeff 144 =
      -((53491222458111 * 10 ^ 70 +
        9127447608666298080670646784178147188563055217056843025332002660440173) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_145 :
    remainder4Coefficient3.coeff 145 =
      ((19450864279384 * 10 ^ 70 +
        1728640833993218764160070826998751519689058802761158483747094531394883) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_146 :
    remainder4Coefficient3.coeff 146 =
      -((6119014773678 * 10 ^ 70 +
        4320553597331358413476387439106794408833006763342657709013383907720059) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_147 :
    remainder4Coefficient3.coeff 147 =
      ((1641951112820 * 10 ^ 70 +
        4446662609155753406954039122145831885462204392141023001306883700933573) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_148 :
    remainder4Coefficient3.coeff 148 =
      -((360610900071 * 10 ^ 70 +
        5812968628521305914460892686792408692100154300407298413718324499120819) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_149 :
    remainder4Coefficient3.coeff 149 =
      ((57338060556 * 10 ^ 70 +
        8532571362967442919059634499209121137006446797194603505400027790593220) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_150 :
    remainder4Coefficient3.coeff 150 =
      -((2941217882 * 10 ^ 70 +
        4040288801601615298919010316219132542834229810049884746544353891877341) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_151 :
    remainder4Coefficient3.coeff 151 =
      -((2029742867 * 10 ^ 70 +
        7215496040348999888451357727922336715341483568452855372131477898983808) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_152 :
    remainder4Coefficient3.coeff 152 =
      ((954851903 * 10 ^ 70 +
        8777118683187602189966660339636999333589401061944063342247707488913605) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_153 :
    remainder4Coefficient3.coeff 153 =
      -((261523293 * 10 ^ 70 +
        3985222630176398449348893763254794386295979768311644249549522726189836) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_154 :
    remainder4Coefficient3.coeff 154 =
      ((52016130 * 10 ^ 70 +
        6250820114246916347297255811826116776870176386468820960141010874861453) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_155 :
    remainder4Coefficient3.coeff 155 =
      -((7529738 * 10 ^ 70 +
        8882614122119469278855918786920959646204592361785392329918892741887177) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_156 :
    remainder4Coefficient3.coeff 156 =
      ((670869 * 10 ^ 70 +
        4149492013070544120504953380494570573173591383761327181896878112378625) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_157 :
    remainder4Coefficient3.coeff 157 =
      ((5034 * 10 ^ 70 +
        0809238367424219424943737840292078553041759656521398811752282801163333) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_158 :
    remainder4Coefficient3.coeff 158 =
      -((13763 * 10 ^ 70 +
        1343868770129886441278872977682933376295326019616474534153022713142713) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_159 :
    remainder4Coefficient3.coeff 159 =
      ((2567 * 10 ^ 70 +
        0159807140849644758810177564916223163366932587566153546114245969394603) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_160 :
    remainder4Coefficient3.coeff 160 =
      -((251 * 10 ^ 70 +
        4755066719672543436122499147806943752112024639429585293293877210446086) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_161 :
    remainder4Coefficient3.coeff 161 =
      ((9 * 10 ^ 70 +
        0123289976735131688284552578404756427201161147311337689855863741669613) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_162 :
    remainder4Coefficient3.coeff 162 =
      ((1 * 10 ^ 70 +
        0357466453028363649478345080173987541246270239173379795289746840122160) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_163 :
    remainder4Coefficient3.coeff 163 =
      (-1591557553516914809999291331010334904183297190859432634267957584619920 : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_164 :
    remainder4Coefficient3.coeff 164 =
      (64192859485147724713156447147442443069571618013590425363183394210221 : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_165 :
    remainder4Coefficient3.coeff 165 =
      (2940659971150785488107316659332768050451821347912167431729729563472 : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_166 :
    remainder4Coefficient3.coeff 166 =
      (-290222416177351659817620430261540261754938427249129014667382600518 : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_167 :
    remainder4Coefficient3.coeff 167 =
      (-2673509468337928237153636781769606259226312833740064163770435640 : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_168 :
    remainder4Coefficient3.coeff 168 =
      (461173632009975689765327354145573282034632690825055134718406706 : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_169 :
    remainder4Coefficient3.coeff 169 =
      (13678359268948244068023964204315217289422925301923569479153708 : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_170 :
    remainder4Coefficient3.coeff 170 =
      (158669650449144170041633734342020405928016706047960043520116 : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_171 :
    remainder4Coefficient3.coeff 171 =
      (898606311527735700700493168659986641592878233361241465839 : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_172 :
    remainder4Coefficient3.coeff 172 =
      (2371664288273465041984725505951593404244237121866404781 : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_173 :
    remainder4Coefficient3.coeff 173 =
      (1179577590987372755814590884987775128001393451772221 : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_174 :
    remainder4Coefficient3.coeff 174 =
      (-7348857963608813800547514573312447633894677203793 : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_175 :
    remainder4Coefficient3.coeff 175 =
      (-14659606690168943660406948437174178003016857730 : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_176 :
    remainder4Coefficient3.coeff 176 =
      (-9455753190036896514754521886556244487895968 : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_177 :
    remainder4Coefficient3.coeff 177 =
      (-2136941820660730238666833940248274697134 : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_178 :
    remainder4Coefficient3.coeff 178 =
      (-149550564265447296005016323537571218 : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_179 :
    remainder4Coefficient3.coeff 179 =
      (-2607303943903993121081377262477 : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_180 :
    remainder4Coefficient3.coeff 180 =
      (-8056366121658586735686137 : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_181 :
    remainder4Coefficient3.coeff 181 =
      (-2461217561584658835 : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_182 :
    remainder4Coefficient3.coeff 182 =
      (-18890099430 : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
