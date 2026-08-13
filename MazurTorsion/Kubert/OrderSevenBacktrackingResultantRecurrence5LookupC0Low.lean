/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData5
import Mathlib.Tactic.NormNum

/-!
# Recurrence 5 lookup certificate: C0 source coefficients, low half

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence5C0_coeff_0 :
    remainder7Coefficient0.coeff 0 =
      -(((5 * 10 ^ 70 +
        4008327283555638291083160230361784252244639539585487364791688780931366) * 10 ^ 70 +
        1824061586378550580354613962901225431925937541092542804380693406304800) : ℚ) := by
  unfold
    remainder7Coefficient0
    remainder7Coefficient0Block0
    remainder7Coefficient0Chunk11
    remainder7Coefficient0Chunk10
    remainder7Coefficient0Chunk9
    remainder7Coefficient0Chunk8
    remainder7Coefficient0Chunk7
    remainder7Coefficient0Chunk6
    remainder7Coefficient0Chunk5
    remainder7Coefficient0Chunk4
    remainder7Coefficient0Chunk3
    remainder7Coefficient0Chunk2
    remainder7Coefficient0Chunk1
    remainder7Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C0_coeff_1 :
    remainder7Coefficient0.coeff 1 =
      (((10920 * 10 ^ 70 +
        4837767349500624570149985791527758038661149041855451608794715043222420) * 10 ^ 70 +
        8252527657429273477029432986277823354245708089121550457762067548305600) : ℚ) := by
  unfold
    remainder7Coefficient0
    remainder7Coefficient0Block0
    remainder7Coefficient0Chunk11
    remainder7Coefficient0Chunk10
    remainder7Coefficient0Chunk9
    remainder7Coefficient0Chunk8
    remainder7Coefficient0Chunk7
    remainder7Coefficient0Chunk6
    remainder7Coefficient0Chunk5
    remainder7Coefficient0Chunk4
    remainder7Coefficient0Chunk3
    remainder7Coefficient0Chunk2
    remainder7Coefficient0Chunk1
    remainder7Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C0_coeff_2 :
    remainder7Coefficient0.coeff 2 =
      (((37056606 * 10 ^ 70 +
        6794969137449109046834315896787996217523928724197092141627918030900238) * 10 ^ 70 +
        0897171869201048474450226049877275784991166048268941348722384076077200) : ℚ) := by
  unfold
    remainder7Coefficient0
    remainder7Coefficient0Block0
    remainder7Coefficient0Chunk11
    remainder7Coefficient0Chunk10
    remainder7Coefficient0Chunk9
    remainder7Coefficient0Chunk8
    remainder7Coefficient0Chunk7
    remainder7Coefficient0Chunk6
    remainder7Coefficient0Chunk5
    remainder7Coefficient0Chunk4
    remainder7Coefficient0Chunk3
    remainder7Coefficient0Chunk2
    remainder7Coefficient0Chunk1
    remainder7Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C0_coeff_3 :
    remainder7Coefficient0.coeff 3 =
      -(((29685144736 * 10 ^ 70 +
        7251553071227876430162800611750701727456853898673457232417806597762217) * 10 ^ 70 +
        3603195517566980673142876375691316186877673573426796307185967142168800) : ℚ) := by
  unfold
    remainder7Coefficient0
    remainder7Coefficient0Block0
    remainder7Coefficient0Chunk11
    remainder7Coefficient0Chunk10
    remainder7Coefficient0Chunk9
    remainder7Coefficient0Chunk8
    remainder7Coefficient0Chunk7
    remainder7Coefficient0Chunk6
    remainder7Coefficient0Chunk5
    remainder7Coefficient0Chunk4
    remainder7Coefficient0Chunk3
    remainder7Coefficient0Chunk2
    remainder7Coefficient0Chunk1
    remainder7Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C0_coeff_4 :
    remainder7Coefficient0.coeff 4 =
      -(((2257044609597 * 10 ^ 70 +
        6822938589408338326052388920057926076042485032028260082797902348687943) * 10 ^ 70 +
        9460318488691017595824262221891538174794705613324040955559449240953600) : ℚ) := by
  unfold
    remainder7Coefficient0
    remainder7Coefficient0Block0
    remainder7Coefficient0Chunk11
    remainder7Coefficient0Chunk10
    remainder7Coefficient0Chunk9
    remainder7Coefficient0Chunk8
    remainder7Coefficient0Chunk7
    remainder7Coefficient0Chunk6
    remainder7Coefficient0Chunk5
    remainder7Coefficient0Chunk4
    remainder7Coefficient0Chunk3
    remainder7Coefficient0Chunk2
    remainder7Coefficient0Chunk1
    remainder7Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C0_coeff_5 :
    remainder7Coefficient0.coeff 5 =
      (((6403982672627040 * 10 ^ 70 +
        1460576182840752297080663960899007766988919182482244098163652352445372) * 10 ^ 70 +
        1605715954123305359662001455050950442721130752305754386772777260770700) : ℚ) := by
  unfold
    remainder7Coefficient0
    remainder7Coefficient0Block0
    remainder7Coefficient0Chunk11
    remainder7Coefficient0Chunk10
    remainder7Coefficient0Chunk9
    remainder7Coefficient0Chunk8
    remainder7Coefficient0Chunk7
    remainder7Coefficient0Chunk6
    remainder7Coefficient0Chunk5
    remainder7Coefficient0Chunk4
    remainder7Coefficient0Chunk3
    remainder7Coefficient0Chunk2
    remainder7Coefficient0Chunk1
    remainder7Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C0_coeff_6 :
    remainder7Coefficient0.coeff 6 =
      -(((2148589780138594739 * 10 ^ 70 +
        6872462937416043360507949971335105054337461569346229800869312469890778) * 10 ^ 70 +
        8585889542620772869502500298078217784697127640322884216129423565217100) : ℚ) := by
  unfold
    remainder7Coefficient0
    remainder7Coefficient0Block0
    remainder7Coefficient0Chunk11
    remainder7Coefficient0Chunk10
    remainder7Coefficient0Chunk9
    remainder7Coefficient0Chunk8
    remainder7Coefficient0Chunk7
    remainder7Coefficient0Chunk6
    remainder7Coefficient0Chunk5
    remainder7Coefficient0Chunk4
    remainder7Coefficient0Chunk3
    remainder7Coefficient0Chunk2
    remainder7Coefficient0Chunk1
    remainder7Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C0_coeff_7 :
    remainder7Coefficient0.coeff 7 =
      (((367473321843981797135 * 10 ^ 70 +
        6933807801686854761951250082254100927936474771832506742769343937478409) * 10 ^ 70 +
        5130289349575617676731374194958115929690551354971829414236359362533900) : ℚ) := by
  unfold
    remainder7Coefficient0
    remainder7Coefficient0Block0
    remainder7Coefficient0Chunk11
    remainder7Coefficient0Chunk10
    remainder7Coefficient0Chunk9
    remainder7Coefficient0Chunk8
    remainder7Coefficient0Chunk7
    remainder7Coefficient0Chunk6
    remainder7Coefficient0Chunk5
    remainder7Coefficient0Chunk4
    remainder7Coefficient0Chunk3
    remainder7Coefficient0Chunk2
    remainder7Coefficient0Chunk1
    remainder7Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C0_coeff_8 :
    remainder7Coefficient0.coeff 8 =
      -(((39288663244435738485404 * 10 ^ 70 +
        0790337944814174563426874527340961431444163042210722043051601199721406) * 10 ^ 70 +
        5213095192362212429178742388950243088235483622763970402445023016841300) : ℚ) := by
  unfold
    remainder7Coefficient0
    remainder7Coefficient0Block0
    remainder7Coefficient0Chunk11
    remainder7Coefficient0Chunk10
    remainder7Coefficient0Chunk9
    remainder7Coefficient0Chunk8
    remainder7Coefficient0Chunk7
    remainder7Coefficient0Chunk6
    remainder7Coefficient0Chunk5
    remainder7Coefficient0Chunk4
    remainder7Coefficient0Chunk3
    remainder7Coefficient0Chunk2
    remainder7Coefficient0Chunk1
    remainder7Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C0_coeff_9 :
    remainder7Coefficient0.coeff 9 =
      (((2875371859269618031392391 * 10 ^ 70 +
        1560899388239389177619046526803421863540392627422182653210108463817618) * 10 ^ 70 +
        5032173299415443992850556472154471857999324830585856791018364208544200) : ℚ) := by
  unfold
    remainder7Coefficient0
    remainder7Coefficient0Block0
    remainder7Coefficient0Chunk11
    remainder7Coefficient0Chunk10
    remainder7Coefficient0Chunk9
    remainder7Coefficient0Chunk8
    remainder7Coefficient0Chunk7
    remainder7Coefficient0Chunk6
    remainder7Coefficient0Chunk5
    remainder7Coefficient0Chunk4
    remainder7Coefficient0Chunk3
    remainder7Coefficient0Chunk2
    remainder7Coefficient0Chunk1
    remainder7Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C0_coeff_10 :
    remainder7Coefficient0.coeff 10 =
      -(((152076381681672063304423058 * 10 ^ 70 +
        3481245391746150032946546650566153464132412558845018396763834181510382) * 10 ^ 70 +
        6701781520259217800220380220284810888421427135341362280514467270913200) : ℚ) := by
  unfold
    remainder7Coefficient0
    remainder7Coefficient0Block0
    remainder7Coefficient0Chunk11
    remainder7Coefficient0Chunk10
    remainder7Coefficient0Chunk9
    remainder7Coefficient0Chunk8
    remainder7Coefficient0Chunk7
    remainder7Coefficient0Chunk6
    remainder7Coefficient0Chunk5
    remainder7Coefficient0Chunk4
    remainder7Coefficient0Chunk3
    remainder7Coefficient0Chunk2
    remainder7Coefficient0Chunk1
    remainder7Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C0_coeff_11 :
    remainder7Coefficient0.coeff 11 =
      (((6033194367033882086910056300 * 10 ^ 70 +
        6147302294718194591814530963510050808391674382909270673515564767458723) * 10 ^ 70 +
        7705964232006953413551753675904093541084624010751688053867513619561300) : ℚ) := by
  unfold
    remainder7Coefficient0
    remainder7Coefficient0Block0
    remainder7Coefficient0Chunk11
    remainder7Coefficient0Chunk10
    remainder7Coefficient0Chunk9
    remainder7Coefficient0Chunk8
    remainder7Coefficient0Chunk7
    remainder7Coefficient0Chunk6
    remainder7Coefficient0Chunk5
    remainder7Coefficient0Chunk4
    remainder7Coefficient0Chunk3
    remainder7Coefficient0Chunk2
    remainder7Coefficient0Chunk1
    remainder7Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C0_coeff_12 :
    remainder7Coefficient0.coeff 12 =
      -(((184593696910905237419974990341 * 10 ^ 70 +
        2930478154602564996682853824868843010513565410294636618180203609493725) * 10 ^ 70 +
        8870995617478605830200074324677611350765232476593425229218482491089100) : ℚ) := by
  unfold
    remainder7Coefficient0
    remainder7Coefficient0Block0
    remainder7Coefficient0Chunk11
    remainder7Coefficient0Chunk10
    remainder7Coefficient0Chunk9
    remainder7Coefficient0Chunk8
    remainder7Coefficient0Chunk7
    remainder7Coefficient0Chunk6
    remainder7Coefficient0Chunk5
    remainder7Coefficient0Chunk4
    remainder7Coefficient0Chunk3
    remainder7Coefficient0Chunk2
    remainder7Coefficient0Chunk1
    remainder7Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C0_coeff_13 :
    remainder7Coefficient0.coeff 13 =
      (((4452576208596100421272364907210 * 10 ^ 70 +
        5111413409605698555397954031768527755566063709355451579853871161714759) * 10 ^ 70 +
        7402637081301277312747675638364189313317704838188258840707476193001900) : ℚ) := by
  unfold
    remainder7Coefficient0
    remainder7Coefficient0Block0
    remainder7Coefficient0Chunk11
    remainder7Coefficient0Chunk10
    remainder7Coefficient0Chunk9
    remainder7Coefficient0Chunk8
    remainder7Coefficient0Chunk7
    remainder7Coefficient0Chunk6
    remainder7Coefficient0Chunk5
    remainder7Coefficient0Chunk4
    remainder7Coefficient0Chunk3
    remainder7Coefficient0Chunk2
    remainder7Coefficient0Chunk1
    remainder7Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C0_coeff_14 :
    remainder7Coefficient0.coeff 14 =
      -(((86224014285193444917747214635760 * 10 ^ 70 +
        0492340925023529217926645810394801883839008115756858989750781891605586) * 10 ^ 70 +
        4562905819878994101054730596142025736687622540985589573730406940008200) : ℚ) := by
  unfold
    remainder7Coefficient0
    remainder7Coefficient0Block0
    remainder7Coefficient0Chunk11
    remainder7Coefficient0Chunk10
    remainder7Coefficient0Chunk9
    remainder7Coefficient0Chunk8
    remainder7Coefficient0Chunk7
    remainder7Coefficient0Chunk6
    remainder7Coefficient0Chunk5
    remainder7Coefficient0Chunk4
    remainder7Coefficient0Chunk3
    remainder7Coefficient0Chunk2
    remainder7Coefficient0Chunk1
    remainder7Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C0_coeff_15 :
    remainder7Coefficient0.coeff 15 =
      (((1361599297502749867498620067801065 * 10 ^ 70 +
        7788834490917529914767648721697990847551767572333408053086095733856060) * 10 ^ 70 +
        9136094081025004910953962604967580094646739044261813255279406799977600) : ℚ) := by
  unfold
    remainder7Coefficient0
    remainder7Coefficient0Block0
    remainder7Coefficient0Chunk11
    remainder7Coefficient0Chunk10
    remainder7Coefficient0Chunk9
    remainder7Coefficient0Chunk8
    remainder7Coefficient0Chunk7
    remainder7Coefficient0Chunk6
    remainder7Coefficient0Chunk5
    remainder7Coefficient0Chunk4
    remainder7Coefficient0Chunk3
    remainder7Coefficient0Chunk2
    remainder7Coefficient0Chunk1
    remainder7Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C0_coeff_16 :
    remainder7Coefficient0.coeff 16 =
      -(((17777294562045989311122708657449169 * 10 ^ 70 +
        3240640625946109074342108318731113546255630049661103412699236088065447) * 10 ^ 70 +
        4232656382533766865302853797560463526062703008976428511003486551759900) : ℚ) := by
  unfold
    remainder7Coefficient0
    remainder7Coefficient0Block0
    remainder7Coefficient0Chunk11
    remainder7Coefficient0Chunk10
    remainder7Coefficient0Chunk9
    remainder7Coefficient0Chunk8
    remainder7Coefficient0Chunk7
    remainder7Coefficient0Chunk6
    remainder7Coefficient0Chunk5
    remainder7Coefficient0Chunk4
    remainder7Coefficient0Chunk3
    remainder7Coefficient0Chunk2
    remainder7Coefficient0Chunk1
    remainder7Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C0_coeff_17 :
    remainder7Coefficient0.coeff 17 =
      (((194301724588211868572972786537566964 * 10 ^ 70 +
        0963102958214510439199395011233202165520569842404976389082316044449135) * 10 ^ 70 +
        7769208009458679257115913293612940909736642465500061144015737217772500) : ℚ) := by
  unfold
    remainder7Coefficient0
    remainder7Coefficient0Block0
    remainder7Coefficient0Chunk11
    remainder7Coefficient0Chunk10
    remainder7Coefficient0Chunk9
    remainder7Coefficient0Chunk8
    remainder7Coefficient0Chunk7
    remainder7Coefficient0Chunk6
    remainder7Coefficient0Chunk5
    remainder7Coefficient0Chunk4
    remainder7Coefficient0Chunk3
    remainder7Coefficient0Chunk2
    remainder7Coefficient0Chunk1
    remainder7Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C0_coeff_18 :
    remainder7Coefficient0.coeff 18 =
      -(((1798080121709546127662088738744036411 * 10 ^ 70 +
        3376495752024373433930007637453646659595459870609649084588485130374364) * 10 ^ 70 +
        6553123387362650462273874688361331993444531945901555147782080780101400) : ℚ) := by
  unfold
    remainder7Coefficient0
    remainder7Coefficient0Block0
    remainder7Coefficient0Chunk11
    remainder7Coefficient0Chunk10
    remainder7Coefficient0Chunk9
    remainder7Coefficient0Chunk8
    remainder7Coefficient0Chunk7
    remainder7Coefficient0Chunk6
    remainder7Coefficient0Chunk5
    remainder7Coefficient0Chunk4
    remainder7Coefficient0Chunk3
    remainder7Coefficient0Chunk2
    remainder7Coefficient0Chunk1
    remainder7Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C0_coeff_19 :
    remainder7Coefficient0.coeff 19 =
      (((14235940781240338753253745476909138053 * 10 ^ 70 +
        6876861938317086141361877050238546972230178789768155714115951559868673) * 10 ^ 70 +
        1061304986576464520822036350986423174162819200086897214025886043994800) : ℚ) := by
  unfold
    remainder7Coefficient0
    remainder7Coefficient0Block0
    remainder7Coefficient0Chunk11
    remainder7Coefficient0Chunk10
    remainder7Coefficient0Chunk9
    remainder7Coefficient0Chunk8
    remainder7Coefficient0Chunk7
    remainder7Coefficient0Chunk6
    remainder7Coefficient0Chunk5
    remainder7Coefficient0Chunk4
    remainder7Coefficient0Chunk3
    remainder7Coefficient0Chunk2
    remainder7Coefficient0Chunk1
    remainder7Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C0_coeff_20 :
    remainder7Coefficient0.coeff 20 =
      -(((97357120273167762252495615253941194289 * 10 ^ 70 +
        3622054930003776938582725646106316751735065058653383694691017667942792) * 10 ^ 70 +
        7934999437870788909029690663242394113335904292040541525928518708542800) : ℚ) := by
  unfold
    remainder7Coefficient0
    remainder7Coefficient0Block0
    remainder7Coefficient0Chunk11
    remainder7Coefficient0Chunk10
    remainder7Coefficient0Chunk9
    remainder7Coefficient0Chunk8
    remainder7Coefficient0Chunk7
    remainder7Coefficient0Chunk6
    remainder7Coefficient0Chunk5
    remainder7Coefficient0Chunk4
    remainder7Coefficient0Chunk3
    remainder7Coefficient0Chunk2
    remainder7Coefficient0Chunk1
    remainder7Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C0_coeff_21 :
    remainder7Coefficient0.coeff 21 =
      (((580194230130158183913998702912652427369 * 10 ^ 70 +
        9692354332791985766106240272032395358632483064322895024240817723133905) * 10 ^ 70 +
        5168452314289598707096439238933028200414595810962461041928692729883200) : ℚ) := by
  unfold
    remainder7Coefficient0
    remainder7Coefficient0Block0
    remainder7Coefficient0Chunk11
    remainder7Coefficient0Chunk10
    remainder7Coefficient0Chunk9
    remainder7Coefficient0Chunk8
    remainder7Coefficient0Chunk7
    remainder7Coefficient0Chunk6
    remainder7Coefficient0Chunk5
    remainder7Coefficient0Chunk4
    remainder7Coefficient0Chunk3
    remainder7Coefficient0Chunk2
    remainder7Coefficient0Chunk1
    remainder7Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C0_coeff_22 :
    remainder7Coefficient0.coeff 22 =
      -(((3037378736139365251490167874204992005105 * 10 ^ 70 +
        5030212669305669249926251508961153665697482815631951581042850842919220) * 10 ^ 70 +
        3320172512858878821323217899151053198876474290079721563974652012182600) : ℚ) := by
  unfold
    remainder7Coefficient0
    remainder7Coefficient0Block0
    remainder7Coefficient0Chunk11
    remainder7Coefficient0Chunk10
    remainder7Coefficient0Chunk9
    remainder7Coefficient0Chunk8
    remainder7Coefficient0Chunk7
    remainder7Coefficient0Chunk6
    remainder7Coefficient0Chunk5
    remainder7Coefficient0Chunk4
    remainder7Coefficient0Chunk3
    remainder7Coefficient0Chunk2
    remainder7Coefficient0Chunk1
    remainder7Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C0_coeff_23 :
    remainder7Coefficient0.coeff 23 =
      (((14071109497484721573050971901511522160324 * 10 ^ 70 +
        1869337458036686184868061814274334003110671441061959487526452365466997) * 10 ^ 70 +
        6468902601568721054310260947602091589021211971832675405834612815415500) : ℚ) := by
  unfold
    remainder7Coefficient0
    remainder7Coefficient0Block0
    remainder7Coefficient0Chunk11
    remainder7Coefficient0Chunk10
    remainder7Coefficient0Chunk9
    remainder7Coefficient0Chunk8
    remainder7Coefficient0Chunk7
    remainder7Coefficient0Chunk6
    remainder7Coefficient0Chunk5
    remainder7Coefficient0Chunk4
    remainder7Coefficient0Chunk3
    remainder7Coefficient0Chunk2
    remainder7Coefficient0Chunk1
    remainder7Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C0_coeff_24 :
    remainder7Coefficient0.coeff 24 =
      -(((58068957256032402917674879616182812609784 * 10 ^ 70 +
        0164676513051435681501053151291217921783941914203283834285481655353220) * 10 ^ 70 +
        6527873210537272779727913568302739593731003990969900729698429238791600) : ℚ) := by
  unfold
    remainder7Coefficient0
    remainder7Coefficient0Block0
    remainder7Coefficient0Chunk11
    remainder7Coefficient0Chunk10
    remainder7Coefficient0Chunk9
    remainder7Coefficient0Chunk8
    remainder7Coefficient0Chunk7
    remainder7Coefficient0Chunk6
    remainder7Coefficient0Chunk5
    remainder7Coefficient0Chunk4
    remainder7Coefficient0Chunk3
    remainder7Coefficient0Chunk2
    remainder7Coefficient0Chunk1
    remainder7Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C0_coeff_25 :
    remainder7Coefficient0.coeff 25 =
      (((214750958558953640255382111941225572657311 * 10 ^ 70 +
        9344724538726288560440360493702223604567196492747618351843925214647158) * 10 ^ 70 +
        1786774591135213942029325102094485111190783169672815749608433058001700) : ℚ) := by
  unfold
    remainder7Coefficient0
    remainder7Coefficient0Block0
    remainder7Coefficient0Chunk11
    remainder7Coefficient0Chunk10
    remainder7Coefficient0Chunk9
    remainder7Coefficient0Chunk8
    remainder7Coefficient0Chunk7
    remainder7Coefficient0Chunk6
    remainder7Coefficient0Chunk5
    remainder7Coefficient0Chunk4
    remainder7Coefficient0Chunk3
    remainder7Coefficient0Chunk2
    remainder7Coefficient0Chunk1
    remainder7Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C0_coeff_26 :
    remainder7Coefficient0.coeff 26 =
      -(((715490041971486516534268012273846984394807 * 10 ^ 70 +
        2728780116391759791458121495701526396956353158284219160582316373371695) * 10 ^ 70 +
        3558372208738266402358172899230627998320105122313124196485552527882200) : ℚ) := by
  unfold
    remainder7Coefficient0
    remainder7Coefficient0Block0
    remainder7Coefficient0Chunk11
    remainder7Coefficient0Chunk10
    remainder7Coefficient0Chunk9
    remainder7Coefficient0Chunk8
    remainder7Coefficient0Chunk7
    remainder7Coefficient0Chunk6
    remainder7Coefficient0Chunk5
    remainder7Coefficient0Chunk4
    remainder7Coefficient0Chunk3
    remainder7Coefficient0Chunk2
    remainder7Coefficient0Chunk1
    remainder7Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C0_coeff_27 :
    remainder7Coefficient0.coeff 27 =
      (((2157590469891245850024113461316626271355194 * 10 ^ 70 +
        1030828701419723083427229031286829185256351585254465012773504476542731) * 10 ^ 70 +
        2774871527701927030409612720661410148382786934564985703129641740385200) : ℚ) := by
  unfold
    remainder7Coefficient0
    remainder7Coefficient0Block0
    remainder7Coefficient0Chunk11
    remainder7Coefficient0Chunk10
    remainder7Coefficient0Chunk9
    remainder7Coefficient0Chunk8
    remainder7Coefficient0Chunk7
    remainder7Coefficient0Chunk6
    remainder7Coefficient0Chunk5
    remainder7Coefficient0Chunk4
    remainder7Coefficient0Chunk3
    remainder7Coefficient0Chunk2
    remainder7Coefficient0Chunk1
    remainder7Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C0_coeff_28 :
    remainder7Coefficient0.coeff 28 =
      -(((5912521435475214592937223600082828360557451 * 10 ^ 70 +
        8534956915164498765118227003169406685165356981548823855939120288776199) * 10 ^ 70 +
        5430820756080774328634229938203703238009251676142333705368266628625500) : ℚ) := by
  unfold
    remainder7Coefficient0
    remainder7Coefficient0Block0
    remainder7Coefficient0Chunk11
    remainder7Coefficient0Chunk10
    remainder7Coefficient0Chunk9
    remainder7Coefficient0Chunk8
    remainder7Coefficient0Chunk7
    remainder7Coefficient0Chunk6
    remainder7Coefficient0Chunk5
    remainder7Coefficient0Chunk4
    remainder7Coefficient0Chunk3
    remainder7Coefficient0Chunk2
    remainder7Coefficient0Chunk1
    remainder7Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C0_coeff_29 :
    remainder7Coefficient0.coeff 29 =
      (((14773508102568993204939607722016805997446475 * 10 ^ 70 +
        0126146117479724556803028924753195582633615679300819985521090537575444) * 10 ^ 70 +
        0713013263601157051303336411394124478971021398239719651662467272051700) : ℚ) := by
  unfold
    remainder7Coefficient0
    remainder7Coefficient0Block0
    remainder7Coefficient0Chunk11
    remainder7Coefficient0Chunk10
    remainder7Coefficient0Chunk9
    remainder7Coefficient0Chunk8
    remainder7Coefficient0Chunk7
    remainder7Coefficient0Chunk6
    remainder7Coefficient0Chunk5
    remainder7Coefficient0Chunk4
    remainder7Coefficient0Chunk3
    remainder7Coefficient0Chunk2
    remainder7Coefficient0Chunk1
    remainder7Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C0_coeff_30 :
    remainder7Coefficient0.coeff 30 =
      -(((33752609807337603107917979018166065367745434 * 10 ^ 70 +
        0247672806195138930344238524237311740475372750334349254267283184656996) * 10 ^ 70 +
        0815052381306851169202218206314648928189563480184959482542810420578900) : ℚ) := by
  unfold
    remainder7Coefficient0
    remainder7Coefficient0Block0
    remainder7Coefficient0Chunk11
    remainder7Coefficient0Chunk10
    remainder7Coefficient0Chunk9
    remainder7Coefficient0Chunk8
    remainder7Coefficient0Chunk7
    remainder7Coefficient0Chunk6
    remainder7Coefficient0Chunk5
    remainder7Coefficient0Chunk4
    remainder7Coefficient0Chunk3
    remainder7Coefficient0Chunk2
    remainder7Coefficient0Chunk1
    remainder7Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C0_coeff_31 :
    remainder7Coefficient0.coeff 31 =
      (((70664346412568966891297133543231525291424840 * 10 ^ 70 +
        6906464440617304417194031803181644688858316475602132716940325988599339) * 10 ^ 70 +
        5837149935596705560392458308908650770534536979646329483712066211672200) : ℚ) := by
  unfold
    remainder7Coefficient0
    remainder7Coefficient0Block0
    remainder7Coefficient0Chunk11
    remainder7Coefficient0Chunk10
    remainder7Coefficient0Chunk9
    remainder7Coefficient0Chunk8
    remainder7Coefficient0Chunk7
    remainder7Coefficient0Chunk6
    remainder7Coefficient0Chunk5
    remainder7Coefficient0Chunk4
    remainder7Coefficient0Chunk3
    remainder7Coefficient0Chunk2
    remainder7Coefficient0Chunk1
    remainder7Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C0_coeff_32 :
    remainder7Coefficient0.coeff 32 =
      -(((135796739869714121949272918154043049582071782 * 10 ^ 70 +
        7743813477926995317165574744684951708774975735403789668138666157974739) * 10 ^ 70 +
        2160450878072140135444575870994831910356029585309763535229729371031100) : ℚ) := by
  unfold
    remainder7Coefficient0
    remainder7Coefficient0Block0
    remainder7Coefficient0Chunk11
    remainder7Coefficient0Chunk10
    remainder7Coefficient0Chunk9
    remainder7Coefficient0Chunk8
    remainder7Coefficient0Chunk7
    remainder7Coefficient0Chunk6
    remainder7Coefficient0Chunk5
    remainder7Coefficient0Chunk4
    remainder7Coefficient0Chunk3
    remainder7Coefficient0Chunk2
    remainder7Coefficient0Chunk1
    remainder7Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C0_coeff_33 :
    remainder7Coefficient0.coeff 33 =
      (((239825547876705949062304134473956538805591761 * 10 ^ 70 +
        5468288602300472479425680699863051617846894004714250043569425374068691) * 10 ^ 70 +
        8869352575602627098908771450997234122519446981612181528631653306795300) : ℚ) := by
  unfold
    remainder7Coefficient0
    remainder7Coefficient0Block0
    remainder7Coefficient0Chunk11
    remainder7Coefficient0Chunk10
    remainder7Coefficient0Chunk9
    remainder7Coefficient0Chunk8
    remainder7Coefficient0Chunk7
    remainder7Coefficient0Chunk6
    remainder7Coefficient0Chunk5
    remainder7Coefficient0Chunk4
    remainder7Coefficient0Chunk3
    remainder7Coefficient0Chunk2
    remainder7Coefficient0Chunk1
    remainder7Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C0_coeff_34 :
    remainder7Coefficient0.coeff 34 =
      -(((389547819470644194018491354853093349634320674 * 10 ^ 70 +
        6217243562688509839867880147547812487846950603179420310615301449805313) * 10 ^ 70 +
        4431146100138067904471047025437350012132347747573170709490533299953800) : ℚ) := by
  unfold
    remainder7Coefficient0
    remainder7Coefficient0Block0
    remainder7Coefficient0Chunk11
    remainder7Coefficient0Chunk10
    remainder7Coefficient0Chunk9
    remainder7Coefficient0Chunk8
    remainder7Coefficient0Chunk7
    remainder7Coefficient0Chunk6
    remainder7Coefficient0Chunk5
    remainder7Coefficient0Chunk4
    remainder7Coefficient0Chunk3
    remainder7Coefficient0Chunk2
    remainder7Coefficient0Chunk1
    remainder7Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C0_coeff_35 :
    remainder7Coefficient0.coeff 35 =
      (((582204022202223191262989097577145350794130463 * 10 ^ 70 +
        4384132372013133859938253329552972469177649827265083839732813512137063) * 10 ^ 70 +
        6650900292038571468684938003389167590736762718458820987273062032549800) : ℚ) := by
  unfold
    remainder7Coefficient0
    remainder7Coefficient0Block0
    remainder7Coefficient0Chunk11
    remainder7Coefficient0Chunk10
    remainder7Coefficient0Chunk9
    remainder7Coefficient0Chunk8
    remainder7Coefficient0Chunk7
    remainder7Coefficient0Chunk6
    remainder7Coefficient0Chunk5
    remainder7Coefficient0Chunk4
    remainder7Coefficient0Chunk3
    remainder7Coefficient0Chunk2
    remainder7Coefficient0Chunk1
    remainder7Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C0_coeff_36 :
    remainder7Coefficient0.coeff 36 =
      -(((800756060549276848275832634883329323730479909 * 10 ^ 70 +
        7295373788196229465216950259100335595471306240774447574182592169738074) * 10 ^ 70 +
        0733370982925477231791048360676542881574606545208815640860699512787600) : ℚ) := by
  unfold
    remainder7Coefficient0
    remainder7Coefficient0Block0
    remainder7Coefficient0Chunk11
    remainder7Coefficient0Chunk10
    remainder7Coefficient0Chunk9
    remainder7Coefficient0Chunk8
    remainder7Coefficient0Chunk7
    remainder7Coefficient0Chunk6
    remainder7Coefficient0Chunk5
    remainder7Coefficient0Chunk4
    remainder7Coefficient0Chunk3
    remainder7Coefficient0Chunk2
    remainder7Coefficient0Chunk1
    remainder7Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C0_coeff_37 :
    remainder7Coefficient0.coeff 37 =
      (((1013415596897760899264844190597686412932434264 * 10 ^ 70 +
        9601227272099781236599588289804704163095470477631998482262783828790233) * 10 ^ 70 +
        4852759539359179407701181802235396577262241133468924665505178723154200) : ℚ) := by
  unfold
    remainder7Coefficient0
    remainder7Coefficient0Block0
    remainder7Coefficient0Chunk11
    remainder7Coefficient0Chunk10
    remainder7Coefficient0Chunk9
    remainder7Coefficient0Chunk8
    remainder7Coefficient0Chunk7
    remainder7Coefficient0Chunk6
    remainder7Coefficient0Chunk5
    remainder7Coefficient0Chunk4
    remainder7Coefficient0Chunk3
    remainder7Coefficient0Chunk2
    remainder7Coefficient0Chunk1
    remainder7Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C0_coeff_38 :
    remainder7Coefficient0.coeff 38 =
      -(((1179749803922032062339197024297899895708295023 * 10 ^ 70 +
        6735073676543863819970554704279834477191992842015132894376050699992172) * 10 ^ 70 +
        2673241884351121994946158545244524494713277067670186906413653507338300) : ℚ) := by
  unfold
    remainder7Coefficient0
    remainder7Coefficient0Block0
    remainder7Coefficient0Chunk11
    remainder7Coefficient0Chunk10
    remainder7Coefficient0Chunk9
    remainder7Coefficient0Chunk8
    remainder7Coefficient0Chunk7
    remainder7Coefficient0Chunk6
    remainder7Coefficient0Chunk5
    remainder7Coefficient0Chunk4
    remainder7Coefficient0Chunk3
    remainder7Coefficient0Chunk2
    remainder7Coefficient0Chunk1
    remainder7Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C0_coeff_39 :
    remainder7Coefficient0.coeff 39 =
      (((1262587205134630151154432367289975166974966370 * 10 ^ 70 +
        5588747567901892974628733782718715615135436509685597478634020840186572) * 10 ^ 70 +
        9908442613227989925152587192808135321720401897648393280291871810928800) : ℚ) := by
  unfold
    remainder7Coefficient0
    remainder7Coefficient0Block0
    remainder7Coefficient0Chunk11
    remainder7Coefficient0Chunk10
    remainder7Coefficient0Chunk9
    remainder7Coefficient0Chunk8
    remainder7Coefficient0Chunk7
    remainder7Coefficient0Chunk6
    remainder7Coefficient0Chunk5
    remainder7Coefficient0Chunk4
    remainder7Coefficient0Chunk3
    remainder7Coefficient0Chunk2
    remainder7Coefficient0Chunk1
    remainder7Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C0_coeff_40 :
    remainder7Coefficient0.coeff 40 =
      -(((1241208416436289093195405228030175578369294424 * 10 ^ 70 +
        2359883239535049665883801119922660034830060886314149001329118877541835) * 10 ^ 70 +
        5224733785862976429810529134112993161205960753055638355674139162242800) : ℚ) := by
  unfold
    remainder7Coefficient0
    remainder7Coefficient0Block0
    remainder7Coefficient0Chunk11
    remainder7Coefficient0Chunk10
    remainder7Coefficient0Chunk9
    remainder7Coefficient0Chunk8
    remainder7Coefficient0Chunk7
    remainder7Coefficient0Chunk6
    remainder7Coefficient0Chunk5
    remainder7Coefficient0Chunk4
    remainder7Coefficient0Chunk3
    remainder7Coefficient0Chunk2
    remainder7Coefficient0Chunk1
    remainder7Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C0_coeff_41 :
    remainder7Coefficient0.coeff 41 =
      (((1119539640858086558654466444403427626054808438 * 10 ^ 70 +
        8873168411829173072338777915224398515913570290511367322106593705199279) * 10 ^ 70 +
        6382040275932912925179318703877394636035522058754717459715159195469700) : ℚ) := by
  unfold
    remainder7Coefficient0
    remainder7Coefficient0Block0
    remainder7Coefficient0Chunk11
    remainder7Coefficient0Chunk10
    remainder7Coefficient0Chunk9
    remainder7Coefficient0Chunk8
    remainder7Coefficient0Chunk7
    remainder7Coefficient0Chunk6
    remainder7Coefficient0Chunk5
    remainder7Coefficient0Chunk4
    remainder7Coefficient0Chunk3
    remainder7Coefficient0Chunk2
    remainder7Coefficient0Chunk1
    remainder7Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C0_coeff_42 :
    remainder7Coefficient0.coeff 42 =
      -(((925001175949113305317030818529578882139424406 * 10 ^ 70 +
        4241309370964925512438112509221160040781737582459858675717314666051955) * 10 ^ 70 +
        7483482058823501701280333905763509886524165084445689759986649889020800) : ℚ) := by
  unfold
    remainder7Coefficient0
    remainder7Coefficient0Block0
    remainder7Coefficient0Chunk11
    remainder7Coefficient0Chunk10
    remainder7Coefficient0Chunk9
    remainder7Coefficient0Chunk8
    remainder7Coefficient0Chunk7
    remainder7Coefficient0Chunk6
    remainder7Coefficient0Chunk5
    remainder7Coefficient0Chunk4
    remainder7Coefficient0Chunk3
    remainder7Coefficient0Chunk2
    remainder7Coefficient0Chunk1
    remainder7Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C0_coeff_43 :
    remainder7Coefficient0.coeff 43 =
      (((698459855055079965625911903353135363528610121 * 10 ^ 70 +
        7099059987328580645110326490939427432955957096059584986388650056256978) * 10 ^ 70 +
        4525684424469563864180492084744468341164616987846950299982256228804600) : ℚ) := by
  unfold
    remainder7Coefficient0
    remainder7Coefficient0Block0
    remainder7Coefficient0Chunk11
    remainder7Coefficient0Chunk10
    remainder7Coefficient0Chunk9
    remainder7Coefficient0Chunk8
    remainder7Coefficient0Chunk7
    remainder7Coefficient0Chunk6
    remainder7Coefficient0Chunk5
    remainder7Coefficient0Chunk4
    remainder7Coefficient0Chunk3
    remainder7Coefficient0Chunk2
    remainder7Coefficient0Chunk1
    remainder7Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C0_coeff_44 :
    remainder7Coefficient0.coeff 44 =
      -(((480322080330864609751306142701685449939643225 * 10 ^ 70 +
        8181914697863458943310154041712343833464060019041662742681364664710250) * 10 ^ 70 +
        3604523819536680419567109824816377133417434714908847737835863845590300) : ℚ) := by
  unfold
    remainder7Coefficient0
    remainder7Coefficient0Block0
    remainder7Coefficient0Chunk11
    remainder7Coefficient0Chunk10
    remainder7Coefficient0Chunk9
    remainder7Coefficient0Chunk8
    remainder7Coefficient0Chunk7
    remainder7Coefficient0Chunk6
    remainder7Coefficient0Chunk5
    remainder7Coefficient0Chunk4
    remainder7Coefficient0Chunk3
    remainder7Coefficient0Chunk2
    remainder7Coefficient0Chunk1
    remainder7Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
