/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData4
import Mathlib.Tactic.NormNum

/-!
# Recurrence 4 lookup certificate: B3 source coefficients, high half

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence4B3_coeff_83 :
    remainder5Coefficient3.coeff 83 =
      -((38866524666380547875837444104940 * 10 ^ 70 +
        0463135121556001943361877811080921396267668670016027569207659636665257) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_84 :
    remainder5Coefficient3.coeff 84 =
      ((105434881176286219116035112835576 * 10 ^ 70 +
        4386147372602646935399683680836246740876085816326599821787753933764121) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_85 :
    remainder5Coefficient3.coeff 85 =
      -((144917089886819899668343951163705 * 10 ^ 70 +
        5850433856894143966257138741104570758797103270625117531443555047211953) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_86 :
    remainder5Coefficient3.coeff 86 =
      ((158843796729181183350641618062268 * 10 ^ 70 +
        6025790967197498871186390511452210992568929896303793887310399367345801) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_87 :
    remainder5Coefficient3.coeff 87 =
      -((152380841997167014450205992970841 * 10 ^ 70 +
        8832074230851428664087615385827018970423589273919066452696707891501460) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_88 :
    remainder5Coefficient3.coeff 88 =
      ((132502910941961766778860435498979 * 10 ^ 70 +
        6296153408421758870203122667828763572723809084994783100811580798174386) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_89 :
    remainder5Coefficient3.coeff 89 =
      -((106196957413207610240661914274181 * 10 ^ 70 +
        5064720109850364858601845053482187707392993546993237957224100253696845) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_90 :
    remainder5Coefficient3.coeff 90 =
      ((79151570986805408699120099583243 * 10 ^ 70 +
        2075256976602656422516788412962736278688107634309273468718726270328490) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_91 :
    remainder5Coefficient3.coeff 91 =
      -((55129287473034259111582574722714 * 10 ^ 70 +
        8596176377546819932522521782095089922869147652794004643231283005387920) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_92 :
    remainder5Coefficient3.coeff 92 =
      ((35966434902340090582175075854111 * 10 ^ 70 +
        5069913435799182198731971762948255036276530914310873996997115188210585) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_93 :
    remainder5Coefficient3.coeff 93 =
      -((21986080137314593993572124509336 * 10 ^ 70 +
        9205853948079244252215688820624060220278917201136457427261272643117317) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_94 :
    remainder5Coefficient3.coeff 94 =
      ((12569921986038285190246301295709 * 10 ^ 70 +
        9458621703552866650256146646246428535862475844601595520750014961922575) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_95 :
    remainder5Coefficient3.coeff 95 =
      -((6687567179750649601175618559701 * 10 ^ 70 +
        6668252114244857721107735725381019049825708945042015472963987458386645) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_96 :
    remainder5Coefficient3.coeff 96 =
      ((3274945748984358533973554765119 * 10 ^ 70 +
        0185701735801513203052829191719772742180992793602736750837031900425450) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_97 :
    remainder5Coefficient3.coeff 97 =
      -((1440722250665432004726932162896 * 10 ^ 70 +
        7962192300751123010066394322808273805571102485226879452623934040197532) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_98 :
    remainder5Coefficient3.coeff 98 =
      ((534635579414320096001818351489 * 10 ^ 70 +
        6913588216391918418763080550667204587086244005748260820257534215077409) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_99 :
    remainder5Coefficient3.coeff 99 =
      -((131314890499990449910642215431 * 10 ^ 70 +
        7983970260228061013870669275419345902411243533189976469720000369779107) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_100 :
    remainder5Coefficient3.coeff 100 =
      -((22256513202262452421416960142 * 10 ^ 70 +
        6431889941553794805633225977656116443036077263229232041502366017897699) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_101 :
    remainder5Coefficient3.coeff 101 =
      ((63765539895758961975962646311 * 10 ^ 70 +
        4489195657552337736017458289577032247764983751711953835334993304935804) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_102 :
    remainder5Coefficient3.coeff 102 =
      -((61736059766702977257720900041 * 10 ^ 70 +
        7255389882194287992375520840483464678266365752902138633838354833933684) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_103 :
    remainder5Coefficient3.coeff 103 =
      ((47045459646322062254384476090 * 10 ^ 70 +
        2433743790701573624896685254758867494447719352162775032376198964277174) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_104 :
    remainder5Coefficient3.coeff 104 =
      -((31883421230393916142372931385 * 10 ^ 70 +
        0291191241315227264395628183421641661266666475481675126440847489171224) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_105 :
    remainder5Coefficient3.coeff 105 =
      ((20014786803757761117594854278 * 10 ^ 70 +
        8532106140057871055305950863729875067015508094831430992273683821966706) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_106 :
    remainder5Coefficient3.coeff 106 =
      -((11833914101911832478839446948 * 10 ^ 70 +
        8612256903224192738769040110069849608597957092215826824489899315112149) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_107 :
    remainder5Coefficient3.coeff 107 =
      ((6635998698761293632313916588 * 10 ^ 70 +
        0634386835836255605862448665025875994467171066670900773853088123753012) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_108 :
    remainder5Coefficient3.coeff 108 =
      -((3537263806839638322101889877 * 10 ^ 70 +
        2018644866931270903514048036210308226195079097618305987229338945651800) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_109 :
    remainder5Coefficient3.coeff 109 =
      ((1791951898693664225315499999 * 10 ^ 70 +
        9209066654989055274430717240781249842781332932532326447028296351846681) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_110 :
    remainder5Coefficient3.coeff 110 =
      -((861311853462650295421391267 * 10 ^ 70 +
        4560088306180548290320138300896978133850331300868575807100128208724786) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_111 :
    remainder5Coefficient3.coeff 111 =
      ((391715821334677356994457970 * 10 ^ 70 +
        0558087061862455915597512523386932145946620362000162525723884758663581) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_112 :
    remainder5Coefficient3.coeff 112 =
      -((167908562084820451374149594 * 10 ^ 70 +
        5608620202432050101733823491895275700332458918650205103665570599069909) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_113 :
    remainder5Coefficient3.coeff 113 =
      ((67472806317180529198800521 * 10 ^ 70 +
        3635744446896161362664664515263421644082910031760677475172099624374038) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_114 :
    remainder5Coefficient3.coeff 114 =
      -((25221732513405105672635134 * 10 ^ 70 +
        7482810008088764554572586945680447609115119151309125347772054877259942) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_115 :
    remainder5Coefficient3.coeff 115 =
      ((8666212257663366710065626 * 10 ^ 70 +
        3360989125947937477347094301236868162860236572730930210981877424116017) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_116 :
    remainder5Coefficient3.coeff 116 =
      -((2682071204279719275428831 * 10 ^ 70 +
        2554736177282735165100334008994346847894094891383993342775134787954509) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_117 :
    remainder5Coefficient3.coeff 117 =
      ((718099623756892137411207 * 10 ^ 70 +
        2338832378787989429550548553779685262606546592832324546168056808858456) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_118 :
    remainder5Coefficient3.coeff 118 =
      -((149754047146599061490275 * 10 ^ 70 +
        9030789110887770194531983158919213357167609295166850298420880139759178) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_119 :
    remainder5Coefficient3.coeff 119 =
      ((14066818375939978447552 * 10 ^ 70 +
        7483336653041955039714876047485002154187596384476111245838011231906044) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_120 :
    remainder5Coefficient3.coeff 120 =
      ((7153267115087379481075 * 10 ^ 70 +
        3738601004821785136892398227263712734217169397486377693901635217713420) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_121 :
    remainder5Coefficient3.coeff 121 =
      -((5571037959944728193364 * 10 ^ 70 +
        7839818693262929463154730085238906187343131443587111363057389849890604) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_122 :
    remainder5Coefficient3.coeff 122 =
      ((2496425329652168959163 * 10 ^ 70 +
        2730586219107887807749854784397869978639458792583844484768424578268574) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_123 :
    remainder5Coefficient3.coeff 123 =
      -((893195493581331439755 * 10 ^ 70 +
        1506312348291388333427412056339945507962724153696335766498496528378212) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_124 :
    remainder5Coefficient3.coeff 124 =
      ((279949140122051847231 * 10 ^ 70 +
        6728094773313306515340519287808161963166150205503215116437248232445686) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_125 :
    remainder5Coefficient3.coeff 125 =
      -((82045205654896499005 * 10 ^ 70 +
        5002630844393361614722555305815029189470766194637034553393481831566015) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_126 :
    remainder5Coefficient3.coeff 126 =
      ((23919097922365774810 * 10 ^ 70 +
        3632316705478465367937017332106330790966047997315844772445794376395698) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_127 :
    remainder5Coefficient3.coeff 127 =
      -((7087895102910589144 * 10 ^ 70 +
        4077205386867391149140616205601285755369880083314353892045332094452362) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_128 :
    remainder5Coefficient3.coeff 128 =
      ((1988211811144196534 * 10 ^ 70 +
        4444227088683247192723031882873092951297742137480563920562845666892917) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_129 :
    remainder5Coefficient3.coeff 129 =
      -((429170244792093409 * 10 ^ 70 +
        3594978665480329275182028819636344591172555247919534270529237303282461) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_130 :
    remainder5Coefficient3.coeff 130 =
      ((16394927632172079 * 10 ^ 70 +
        4123304788303407181147077219244260079596964970848652196270666501217506) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_131 :
    remainder5Coefficient3.coeff 131 =
      ((47923566457021272 * 10 ^ 70 +
        8919564065579675767190237270157057793142933814753734818123395084871501) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_132 :
    remainder5Coefficient3.coeff 132 =
      -((34027882878653173 * 10 ^ 70 +
        5559687891473258478739168418832766435238815372726621843558034028528531) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_133 :
    remainder5Coefficient3.coeff 133 =
      ((16734293580497187 * 10 ^ 70 +
        3192460633887513726281493467513867022753847600585226996924735295029124) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_134 :
    remainder5Coefficient3.coeff 134 =
      -((7276315826067875 * 10 ^ 70 +
        5337844594360375077406408494129592083958167958112185652274142691347588) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_135 :
    remainder5Coefficient3.coeff 135 =
      ((3052004246526034 * 10 ^ 70 +
        6285091038109868691844960508344423590935707479148947414175404196855425) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_136 :
    remainder5Coefficient3.coeff 136 =
      -((1252352536157476 * 10 ^ 70 +
        4294614329760815953036187985899619841761358228946124415375473325316301) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_137 :
    remainder5Coefficient3.coeff 137 =
      ((490086019343389 * 10 ^ 70 +
        0666563362201878453880494878598837376754885055526032164126822548355779) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_138 :
    remainder5Coefficient3.coeff 138 =
      -((177680969145688 * 10 ^ 70 +
        1943785531615753838205815329909910410031223867315661663299633748769632) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_139 :
    remainder5Coefficient3.coeff 139 =
      ((58672027318845 * 10 ^ 70 +
        9583933738652132260962959360806876609816532021610475873984094855579144) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_140 :
    remainder5Coefficient3.coeff 140 =
      -((17523655908987 * 10 ^ 70 +
        7808981551880645915088830573668170689051267646364616009853068412381126) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_141 :
    remainder5Coefficient3.coeff 141 =
      ((4719695436388 * 10 ^ 70 +
        9639310025966502297891576706146950088813340304074227493651028770551507) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_142 :
    remainder5Coefficient3.coeff 142 =
      -((1142002140033 * 10 ^ 70 +
        6454920949718300868914805238703351531471563501638538982241130917012180) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_143 :
    remainder5Coefficient3.coeff 143 =
      ((246577578629 * 10 ^ 70 +
        8360843595338571701530320934762205654968001848214092633662211486208236) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_144 :
    remainder5Coefficient3.coeff 144 =
      -((47030080520 * 10 ^ 70 +
        8114431842106427346933256177582164650114592401381382322065608472866408) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_145 :
    remainder5Coefficient3.coeff 145 =
      ((7820287055 * 10 ^ 70 +
        7193673705063847092219873265125510273993295296249092569605768787726447) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_146 :
    remainder5Coefficient3.coeff 146 =
      -((1115536633 * 10 ^ 70 +
        1952180484080311972236737136082337622405845563655525665927588269196789) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_147 :
    remainder5Coefficient3.coeff 147 =
      ((133781693 * 10 ^ 70 +
        4470209109764542348822037942549792825924635984366536167159122902603647) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_148 :
    remainder5Coefficient3.coeff 148 =
      -((13131959 * 10 ^ 70 +
        6370032493029726392368481496909338105613298368327001969328293681842791) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_149 :
    remainder5Coefficient3.coeff 149 =
      ((1015604 * 10 ^ 70 +
        4714784963104680389751730198818462215040446882376720092826248007019278) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_150 :
    remainder5Coefficient3.coeff 150 =
      -((58390 * 10 ^ 70 +
        1959169823620478784665064289498459448642811587137818129067006798624831) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_151 :
    remainder5Coefficient3.coeff 151 =
      ((2266 * 10 ^ 70 +
        2063717219107911485446457576525190668901308954367462719133703628939739) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_152 :
    remainder5Coefficient3.coeff 152 =
      -((49 * 10 ^ 70 +
        3192305225148937266252799061341011193663669472250138318183586520266448) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_153 :
    remainder5Coefficient3.coeff 153 =
      (3569551290947626014550370920088617484593554421017738743263080005527564 : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_154 :
    remainder5Coefficient3.coeff 154 =
      (15364874460241919274310490770747333416206943644342775551943578689598 : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_155 :
    remainder5Coefficient3.coeff 155 =
      (-154482697540332732953226464329676070749837843645479196701309115059 : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_156 :
    remainder5Coefficient3.coeff 156 =
      (-11667054656340848662684049708286368298828614767731465825095689 : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_157 :
    remainder5Coefficient3.coeff 157 =
      (1339932918728827906856052854523919863221616769269288116977253 : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_158 :
    remainder5Coefficient3.coeff 158 =
      (-2258019364603840472915416091506789967149902086294606087436 : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_159 :
    remainder5Coefficient3.coeff 159 =
      (1114441137360318994499517012134430527617844825944987556 : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_160 :
    remainder5Coefficient3.coeff 160 =
      (-153773405756152491463125105370326757909641795149761 : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_161 :
    remainder5Coefficient3.coeff 161 =
      (4932242405094780241174003775565952210999946079 : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_162 :
    remainder5Coefficient3.coeff 162 =
      (-27544084507760918430706034189549153086265 : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_163 :
    remainder5Coefficient3.coeff 163 =
      (16735719307940309486145372463218633 : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B3_coeff_164 :
    remainder5Coefficient3.coeff 164 =
      (-447151549834258283177195510 : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
