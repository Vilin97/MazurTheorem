/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData5
import Mathlib.Tactic.NormNum

/-!
# Recurrence 5 lookup certificate: B1 source coefficients, high half

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence5B1_coeff_75 :
    remainder6Coefficient1.coeff 75 =
      ((1154270265138359719765953205865534058318303213631564591467 * 10 ^ 70 +
        2073250351166978331882884341121168502501804827302552623294938783761793) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_76 :
    remainder6Coefficient1.coeff 76 =
      -((685161801818866287906254432959299799276404937948173247757 * 10 ^ 70 +
        8062286382568689410873482648020191019881650787116025737581847360657015) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_77 :
    remainder6Coefficient1.coeff 77 =
      ((378920102370771917345133552648812828343569852294095421213 * 10 ^ 70 +
        0169698262241209990569630467070873083289439126924509694200992144668506) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_78 :
    remainder6Coefficient1.coeff 78 =
      -((191444687266333380179892877302581818649719084675270361370 * 10 ^ 70 +
        4287461742402222948841988301923513652137343768067080730446228358525468) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_79 :
    remainder6Coefficient1.coeff 79 =
      ((84338314273363073264178781464425011473971714081183835555 * 10 ^ 70 +
        0115924547937373030374205014818990315580312971575267640590773481917649) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_80 :
    remainder6Coefficient1.coeff 80 =
      -((27975531726910796170629283133770493712121590784189970056 * 10 ^ 70 +
        8746480769165324308198999344427534584545996119666813504246203913815390) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_81 :
    remainder6Coefficient1.coeff 81 =
      ((1550955308605687611317560129696952330848425612789211457 * 10 ^ 70 +
        2976813682601538271786810089499259869655034171379893587142832938676685) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_82 :
    remainder6Coefficient1.coeff 82 =
      ((8456502098440713929006587439643596350522231315549839825 * 10 ^ 70 +
        1861744150035278660193983448540380986298984183689109302634478912362209) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_83 :
    remainder6Coefficient1.coeff 83 =
      -((10268334201198006680500957200367042791977787670440405785 * 10 ^ 70 +
        2613091914663102185278613799912430805996445193032404923958908487321246) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_84 :
    remainder6Coefficient1.coeff 84 =
      ((8583043054893649966071658674890429196086239619861830680 * 10 ^ 70 +
        9720804189440667551228933597312792300773772695913255241730492934086065) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_85 :
    remainder6Coefficient1.coeff 85 =
      -((5902803915561175860092550935930297255734246112815491593 * 10 ^ 70 +
        5429436398206621288940058725591876111803672994408070545605643083061045) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_86 :
    remainder6Coefficient1.coeff 86 =
      ((3421658654500921030320260530518031813784469567969454177 * 10 ^ 70 +
        1418270584347836848963074795133974247163280379909193401196975470087158) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_87 :
    remainder6Coefficient1.coeff 87 =
      -((1586441137958284647278633539200930203937489422856527033 * 10 ^ 70 +
        4750485873469647986260725340639363767952581090835115747143794740762354) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_88 :
    remainder6Coefficient1.coeff 88 =
      ((445070093823272459557559375423842389274275349636962300 * 10 ^ 70 +
        3663819670152780705435268695951517846023062641919597387628912580057583) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_89 :
    remainder6Coefficient1.coeff 89 =
      ((137204949689062662093237197987475411602454945034546486 * 10 ^ 70 +
        5094377831562001427887861599747121889868415880543970424099524341516034) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_90 :
    remainder6Coefficient1.coeff 90 =
      -((347174485685224579837646805490020331029192869500809253 * 10 ^ 70 +
        5595942372384934901000574990194023980695547378913032399226443612986886) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_91 :
    remainder6Coefficient1.coeff 91 =
      ((352736336785944888331772464491407197829639611733918196 * 10 ^ 70 +
        8594268332024749950693262385740422803371466856691625630264378735739173) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_92 :
    remainder6Coefficient1.coeff 92 =
      -((273969851113590329287184684064449216034331245206675633 * 10 ^ 70 +
        9186359004622901902549166842379623352897173787818959260825604197664068) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_93 :
    remainder6Coefficient1.coeff 93 =
      ((180990738687334526289848457060027281444754220957718745 * 10 ^ 70 +
        7702868846686209288456514424533490247079517653996568758047231135412495) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_94 :
    remainder6Coefficient1.coeff 94 =
      -((105285248332763603363716762203566065944458095080018667 * 10 ^ 70 +
        0497072084678631616465205603676911176232033248192861835494761690819946) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_95 :
    remainder6Coefficient1.coeff 95 =
      ((54534005457720561293975341179142788364343285211288187 * 10 ^ 70 +
        5299811979016691651109633063105329609467242387877234137820729034752346) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_96 :
    remainder6Coefficient1.coeff 96 =
      -((25104459311939175883045948001298090652572814211081892 * 10 ^ 70 +
        2023819234990876488608880207074105698631233612109648258929284938273956) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_97 :
    remainder6Coefficient1.coeff 97 =
      ((10120506992285151514525922178581257079768043588165378 * 10 ^ 70 +
        5668291615438972587597435054643389148568813785648074891781877281724383) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_98 :
    remainder6Coefficient1.coeff 98 =
      -((3440388362528692268321137449457645846998605336708516 * 10 ^ 70 +
        7277874160945709720387909151657168176543433495206986825855666134161245) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_99 :
    remainder6Coefficient1.coeff 99 =
      ((887074932344815173795465324130901740073228739591474 * 10 ^ 70 +
        8814049820256224835110907387955642308616825460238633395754203405622980) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_100 :
    remainder6Coefficient1.coeff 100 =
      -((98027765115768800191911583411845842120722506872444 * 10 ^ 70 +
        8382910785708774676542965492434106903642892443267324909282460265423096) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_101 :
    remainder6Coefficient1.coeff 101 =
      -((62561788123545397580863085053085115144528291886696 * 10 ^ 70 +
        0788739157503586362341333620898740315294667259233823988801385325491241) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_102 :
    remainder6Coefficient1.coeff 102 =
      ((54267662516461575961093203387368223881926423158284 * 10 ^ 70 +
        8387939097642168060588106532302817644806049355702180708867847820770227) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_103 :
    remainder6Coefficient1.coeff 103 =
      -((25738488584203158992145564824567545218365973101812 * 10 ^ 70 +
        3087101611968236256432910754102886554583196964673086139336575315673433) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_104 :
    remainder6Coefficient1.coeff 104 =
      ((8685051171822130775843165283271194307617661821496 * 10 ^ 70 +
        2251450739651530174701514334588353330835885599947728409947148589215324) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_105 :
    remainder6Coefficient1.coeff 105 =
      -((1942749481208239880063953754514400705981608514321 * 10 ^ 70 +
        0010510093578556344270240765061750618480815767393951945482042907668166) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_106 :
    remainder6Coefficient1.coeff 106 =
      ((86322489634214490114693889993353131621688131467 * 10 ^ 70 +
        1913883269136489924968918189170357085510416963502915632604204846104461) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_107 :
    remainder6Coefficient1.coeff 107 =
      ((164531370329407496757809493714988569509650919529 * 10 ^ 70 +
        3730724561479623170009021657346537615830242465865849073936738562356231) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_108 :
    remainder6Coefficient1.coeff 108 =
      -((89519114834803389143289175222077621621490607674 * 10 ^ 70 +
        0917327401398749592294380042434044272110664826469163974638733907081894) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_109 :
    remainder6Coefficient1.coeff 109 =
      ((23147762769213085809247975736995332719965530539 * 10 ^ 70 +
        2429922897045475294463153488426465565977224913678298192111251414732547) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_110 :
    remainder6Coefficient1.coeff 110 =
      ((1343933558309687265710403859269275244891486760 * 10 ^ 70 +
        1087674379796182774433257309732693786320075501608038098368433791310852) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_111 :
    remainder6Coefficient1.coeff 111 =
      -((5206612032616045209766225500545791019414700796 * 10 ^ 70 +
        1687501055683229030970964140348127274019301647841484602083401521990403) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_112 :
    remainder6Coefficient1.coeff 112 =
      ((3540548772594501504188903888229467886897206608 * 10 ^ 70 +
        2445400632703836219891283256551621567970158538433600415304710692375072) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_113 :
    remainder6Coefficient1.coeff 113 =
      -((1720277643999383696387678062412348712293093404 * 10 ^ 70 +
        1744721185740641918961093036955732745050448644081263914454527713920703) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_114 :
    remainder6Coefficient1.coeff 114 =
      ((696419018532600844788025502121215886236319259 * 10 ^ 70 +
        4347554417049489229608534391893233915209105825177048746114340507708666) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_115 :
    remainder6Coefficient1.coeff 115 =
      -((246903864922899889859454457534914025179373890 * 10 ^ 70 +
        2206000055036710824764505978757925685361288544570709990224307950221127) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_116 :
    remainder6Coefficient1.coeff 116 =
      ((77956841766276524417472121095872793545452570 * 10 ^ 70 +
        5784481470272484278402926456076099964945859586779304766963807701763694) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_117 :
    remainder6Coefficient1.coeff 117 =
      -((21963519064196485882710550330413010633571928 * 10 ^ 70 +
        0079546073203956274427304863417207774002688462261311730056638497046287) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_118 :
    remainder6Coefficient1.coeff 118 =
      ((5537448780653919874520601323525710933761850 * 10 ^ 70 +
        9515118826107479429670551686426644008769938849642702727679857334338009) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_119 :
    remainder6Coefficient1.coeff 119 =
      -((1305601355613210298967591926759281967701527 * 10 ^ 70 +
        6331023426673443743332814755445182054243327435672551585952764248210844) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_120 :
    remainder6Coefficient1.coeff 120 =
      ((341040722840907866582810817667619543180244 * 10 ^ 70 +
        6157437790334241042458321349988561064383117922932411899279445786632107) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_121 :
    remainder6Coefficient1.coeff 121 =
      -((121674460747833619201588455085181382860924 * 10 ^ 70 +
        9280634696285054386383462173968890814463521090220749994366642681418741) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_122 :
    remainder6Coefficient1.coeff 122 =
      ((51983222828032136388646003802553007887284 * 10 ^ 70 +
        0104134479418131176682621789545177403421787249823176788904697138846666) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_123 :
    remainder6Coefficient1.coeff 123 =
      -((19842671323663323661005720429532245069051 * 10 ^ 70 +
        7551770233144465211972927955281072390849646233421855559183379426005529) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_124 :
    remainder6Coefficient1.coeff 124 =
      ((5451129873403708577275998085715805377455 * 10 ^ 70 +
        7783862775793514972588060756332610618462118740333707130043737107842143) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_125 :
    remainder6Coefficient1.coeff 125 =
      -((625435260518757921663823008080639513589 * 10 ^ 70 +
        3151896033066280059717213729603099763733912194741921268671345225448929) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_126 :
    remainder6Coefficient1.coeff 126 =
      -((286366982590787859482206625159615770937 * 10 ^ 70 +
        8875949908525472987729943373481909178798087368626360203546765828519209) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_127 :
    remainder6Coefficient1.coeff 127 =
      ((197506522521232275086687425574345420671 * 10 ^ 70 +
        1711210311496261254557390411882909698569347464810665487598452211098557) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_128 :
    remainder6Coefficient1.coeff 128 =
      -((60830294695569801360761037521699299886 * 10 ^ 70 +
        6860525058621457418858614740197553853103935458643031426354424720903154) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_129 :
    remainder6Coefficient1.coeff 129 =
      ((9522298009204712297569444421461587133 * 10 ^ 70 +
        2705221622810541086002808161247410402647594213638835167691335271064131) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_130 :
    remainder6Coefficient1.coeff 130 =
      ((258828480313644493916178626345488584 * 10 ^ 70 +
        2717088312381096053650847975618770491015055279986733413027549016216185) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_131 :
    remainder6Coefficient1.coeff 131 =
      -((509512592300535163754080979638484406 * 10 ^ 70 +
        0851596378596963679569040075145594499774860797369670472817901562072997) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_132 :
    remainder6Coefficient1.coeff 132 =
      ((115937737541940505607296811439223673 * 10 ^ 70 +
        9520481659138147557553256427363060119742289819752347517878416937064247) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_133 :
    remainder6Coefficient1.coeff 133 =
      -((9348789702628001480647416604683777 * 10 ^ 70 +
        9444390926672611701935644295781567068004682580893310007851117104803594) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_134 :
    remainder6Coefficient1.coeff 134 =
      -((933992615818940833570174961126163 * 10 ^ 70 +
        6824324470241418691656332934992540780638057708493036788398301245774498) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_135 :
    remainder6Coefficient1.coeff 135 =
      ((260828609272442145768978047076574 * 10 ^ 70 +
        6208636141461047205241478762435786001448722784840830312534764587957988) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_136 :
    remainder6Coefficient1.coeff 136 =
      -((11706967069952183782069159675975 * 10 ^ 70 +
        4349292315453241278585467583027424089462593383792660162071497598908284) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_137 :
    remainder6Coefficient1.coeff 137 =
      -((1484714773925873340478380428976 * 10 ^ 70 +
        6209456714728483267570053731560621473013019815861025937280585051869233) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_138 :
    remainder6Coefficient1.coeff 138 =
      ((90003772774382488960151785956 * 10 ^ 70 +
        3478351003670230439238822762218873977565584383521493137806380443916840) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_139 :
    remainder6Coefficient1.coeff 139 =
      ((6014220761540530792059483909 * 10 ^ 70 +
        4053223200543425906232697160456951558514825568150186308120016174160502) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_140 :
    remainder6Coefficient1.coeff 140 =
      ((96161742515874977766067440 * 10 ^ 70 +
        6625576432406338018843556455635943982316685542290021499760390425003809) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_141 :
    remainder6Coefficient1.coeff 141 =
      ((594044152761729338653832 * 10 ^ 70 +
        4371135481404641225337611082632591506252611800049687549228797373908163) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_142 :
    remainder6Coefficient1.coeff 142 =
      ((1310243206025415362987 * 10 ^ 70 +
        1444325639159976235328633735367031516640743348334029435914711762575098) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_143 :
    remainder6Coefficient1.coeff 143 =
      -((727222713217640600 * 10 ^ 70 +
        3823873659395614171621992934013582615542330284707209586966815372251396) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_144 :
    remainder6Coefficient1.coeff 144 =
      -((5742015963620506 * 10 ^ 70 +
        4710592359166180789257254418168783953665238836762637298543757474447430) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_145 :
    remainder6Coefficient1.coeff 145 =
      -((4341270233090 * 10 ^ 70 +
        4286326232859974590492799536994458815149400020241525158973634391722901) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_146 :
    remainder6Coefficient1.coeff 146 =
      -((588377445 * 10 ^ 70 +
        9885319468338569103709477649000773802423121473501199313940396348357272) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_147 :
    remainder6Coefficient1.coeff 147 =
      -((10684 * 10 ^ 70 +
        6565923750474979392317429610767026054979591494449844632283787443967525) : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_148 :
    remainder6Coefficient1.coeff 148 =
      (-140958269732036509305138576524185776416000719009241861107199462994463 : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B1_coeff_149 :
    remainder6Coefficient1.coeff 149 =
      (-5549041120153585801193546258062638078959319258914876744495111 : ℚ) := by
  unfold
    remainder6Coefficient1
    remainder6Coefficient1Block1
    remainder6Coefficient1Block0
    remainder6Coefficient1Chunk18
    remainder6Coefficient1Chunk17
    remainder6Coefficient1Chunk16
    remainder6Coefficient1Chunk15
    remainder6Coefficient1Chunk14
    remainder6Coefficient1Chunk13
    remainder6Coefficient1Chunk12
    remainder6Coefficient1Chunk11
    remainder6Coefficient1Chunk10
    remainder6Coefficient1Chunk9
    remainder6Coefficient1Chunk8
    remainder6Coefficient1Chunk7
    remainder6Coefficient1Chunk6
    remainder6Coefficient1Chunk5
    remainder6Coefficient1Chunk4
    remainder6Coefficient1Chunk3
    remainder6Coefficient1Chunk2
    remainder6Coefficient1Chunk1
    remainder6Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
