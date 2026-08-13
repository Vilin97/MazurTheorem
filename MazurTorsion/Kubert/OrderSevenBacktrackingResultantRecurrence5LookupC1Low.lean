/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData5
import Mathlib.Tactic.NormNum

/-!
# Recurrence 5 lookup certificate: C1 source coefficients, low half

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence5C1_coeff_0 :
    remainder7Coefficient1.coeff 0 =
      -(((109 * 10 ^ 70 +
        3668627492001675394433994664826131107953950676606119137031697813860165) * 10 ^ 70 +
        1937247124165649252180932748749814996500235207123991788709041477672200) : ℚ) := by
  unfold
    remainder7Coefficient1
    remainder7Coefficient1Block0
    remainder7Coefficient1Chunk10
    remainder7Coefficient1Chunk9
    remainder7Coefficient1Chunk8
    remainder7Coefficient1Chunk7
    remainder7Coefficient1Chunk6
    remainder7Coefficient1Chunk5
    remainder7Coefficient1Chunk4
    remainder7Coefficient1Chunk3
    remainder7Coefficient1Chunk2
    remainder7Coefficient1Chunk1
    remainder7Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C1_coeff_1 :
    remainder7Coefficient1.coeff 1 =
      -(((411856 * 10 ^ 70 +
        7021989385864801419632846928943507671722009710095464284603056264122337) * 10 ^ 70 +
        9288454055510156682151582921648987808145008635129176462917777991438400) : ℚ) := by
  unfold
    remainder7Coefficient1
    remainder7Coefficient1Block0
    remainder7Coefficient1Chunk10
    remainder7Coefficient1Chunk9
    remainder7Coefficient1Chunk8
    remainder7Coefficient1Chunk7
    remainder7Coefficient1Chunk6
    remainder7Coefficient1Chunk5
    remainder7Coefficient1Chunk4
    remainder7Coefficient1Chunk3
    remainder7Coefficient1Chunk2
    remainder7Coefficient1Chunk1
    remainder7Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C1_coeff_2 :
    remainder7Coefficient1.coeff 2 =
      (((762377747 * 10 ^ 70 +
        0986388098888851548343857347941185800242811413127261816165292069859502) * 10 ^ 70 +
        4849854786017886382443560590233267625422078798389380098321000880997000) : ℚ) := by
  unfold
    remainder7Coefficient1
    remainder7Coefficient1Block0
    remainder7Coefficient1Chunk10
    remainder7Coefficient1Chunk9
    remainder7Coefficient1Chunk8
    remainder7Coefficient1Chunk7
    remainder7Coefficient1Chunk6
    remainder7Coefficient1Chunk5
    remainder7Coefficient1Chunk4
    remainder7Coefficient1Chunk3
    remainder7Coefficient1Chunk2
    remainder7Coefficient1Chunk1
    remainder7Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C1_coeff_3 :
    remainder7Coefficient1.coeff 3 =
      -(((145441458811 * 10 ^ 70 +
        9653436842313526709245467080046300180736670641822305297657712287545387) * 10 ^ 70 +
        7906278101660165064015725950286781492557028336426161709989915657337000) : ℚ) := by
  unfold
    remainder7Coefficient1
    remainder7Coefficient1Block0
    remainder7Coefficient1Chunk10
    remainder7Coefficient1Chunk9
    remainder7Coefficient1Chunk8
    remainder7Coefficient1Chunk7
    remainder7Coefficient1Chunk6
    remainder7Coefficient1Chunk5
    remainder7Coefficient1Chunk4
    remainder7Coefficient1Chunk3
    remainder7Coefficient1Chunk2
    remainder7Coefficient1Chunk1
    remainder7Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C1_coeff_4 :
    remainder7Coefficient1.coeff 4 =
      -(((138556532012103 * 10 ^ 70 +
        3975198605840846354154170019905265654454453416446069980427988428040321) * 10 ^ 70 +
        2994634670917893690499705192677293385064868561025254480754331642946400) : ℚ) := by
  unfold
    remainder7Coefficient1
    remainder7Coefficient1Block0
    remainder7Coefficient1Chunk10
    remainder7Coefficient1Chunk9
    remainder7Coefficient1Chunk8
    remainder7Coefficient1Chunk7
    remainder7Coefficient1Chunk6
    remainder7Coefficient1Chunk5
    remainder7Coefficient1Chunk4
    remainder7Coefficient1Chunk3
    remainder7Coefficient1Chunk2
    remainder7Coefficient1Chunk1
    remainder7Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C1_coeff_5 :
    remainder7Coefficient1.coeff 5 =
      (((74854218712560599 * 10 ^ 70 +
        2010777661859876844618552530580663051834748197324175845432234499467422) * 10 ^ 70 +
        7870290702494367420335885311521367421522866099947998770234370402906500) : ℚ) := by
  unfold
    remainder7Coefficient1
    remainder7Coefficient1Block0
    remainder7Coefficient1Chunk10
    remainder7Coefficient1Chunk9
    remainder7Coefficient1Chunk8
    remainder7Coefficient1Chunk7
    remainder7Coefficient1Chunk6
    remainder7Coefficient1Chunk5
    remainder7Coefficient1Chunk4
    remainder7Coefficient1Chunk3
    remainder7Coefficient1Chunk2
    remainder7Coefficient1Chunk1
    remainder7Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C1_coeff_6 :
    remainder7Coefficient1.coeff 6 =
      -(((16873892559123085835 * 10 ^ 70 +
        3780442667103577420728735496422611536375282160611561225962296571796198) * 10 ^ 70 +
        7623278518573489167519937635217186435062667325941742127638533878811800) : ℚ) := by
  unfold
    remainder7Coefficient1
    remainder7Coefficient1Block0
    remainder7Coefficient1Chunk10
    remainder7Coefficient1Chunk9
    remainder7Coefficient1Chunk8
    remainder7Coefficient1Chunk7
    remainder7Coefficient1Chunk6
    remainder7Coefficient1Chunk5
    remainder7Coefficient1Chunk4
    remainder7Coefficient1Chunk3
    remainder7Coefficient1Chunk2
    remainder7Coefficient1Chunk1
    remainder7Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C1_coeff_7 :
    remainder7Coefficient1.coeff 7 =
      (((2233000481520792879329 * 10 ^ 70 +
        8678750096197631603885317806520408919909662702297924463184665157570809) * 10 ^ 70 +
        4733086844997534028584545660859474043057248400834914705175965088644800) : ℚ) := by
  unfold
    remainder7Coefficient1
    remainder7Coefficient1Block0
    remainder7Coefficient1Chunk10
    remainder7Coefficient1Chunk9
    remainder7Coefficient1Chunk8
    remainder7Coefficient1Chunk7
    remainder7Coefficient1Chunk6
    remainder7Coefficient1Chunk5
    remainder7Coefficient1Chunk4
    remainder7Coefficient1Chunk3
    remainder7Coefficient1Chunk2
    remainder7Coefficient1Chunk1
    remainder7Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C1_coeff_8 :
    remainder7Coefficient1.coeff 8 =
      -(((195491416419199090236814 * 10 ^ 70 +
        1975381369990162424440786843379630551618741995945361414988617795859607) * 10 ^ 70 +
        4488767957052314242354548575551537257346061231574012722735196902183200) : ℚ) := by
  unfold
    remainder7Coefficient1
    remainder7Coefficient1Block0
    remainder7Coefficient1Chunk10
    remainder7Coefficient1Chunk9
    remainder7Coefficient1Chunk8
    remainder7Coefficient1Chunk7
    remainder7Coefficient1Chunk6
    remainder7Coefficient1Chunk5
    remainder7Coefficient1Chunk4
    remainder7Coefficient1Chunk3
    remainder7Coefficient1Chunk2
    remainder7Coefficient1Chunk1
    remainder7Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C1_coeff_9 :
    remainder7Coefficient1.coeff 9 =
      (((12086142547850230063625001 * 10 ^ 70 +
        1211988398264523881621391908170849688840662341659353401315351592641373) * 10 ^ 70 +
        4625183727496705626701851749217433624022490601601808137007524256245500) : ℚ) := by
  unfold
    remainder7Coefficient1
    remainder7Coefficient1Block0
    remainder7Coefficient1Chunk10
    remainder7Coefficient1Chunk9
    remainder7Coefficient1Chunk8
    remainder7Coefficient1Chunk7
    remainder7Coefficient1Chunk6
    remainder7Coefficient1Chunk5
    remainder7Coefficient1Chunk4
    remainder7Coefficient1Chunk3
    remainder7Coefficient1Chunk2
    remainder7Coefficient1Chunk1
    remainder7Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C1_coeff_10 :
    remainder7Coefficient1.coeff 10 =
      -(((550726776995296454140907365 * 10 ^ 70 +
        7050465634712291635899289244891463601723618735601375317796476071024389) * 10 ^ 70 +
        9859759412395042427528971257462654326960305554783701287120527712876800) : ℚ) := by
  unfold
    remainder7Coefficient1
    remainder7Coefficient1Block0
    remainder7Coefficient1Chunk10
    remainder7Coefficient1Chunk9
    remainder7Coefficient1Chunk8
    remainder7Coefficient1Chunk7
    remainder7Coefficient1Chunk6
    remainder7Coefficient1Chunk5
    remainder7Coefficient1Chunk4
    remainder7Coefficient1Chunk3
    remainder7Coefficient1Chunk2
    remainder7Coefficient1Chunk1
    remainder7Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C1_coeff_11 :
    remainder7Coefficient1.coeff 11 =
      (((19075241550952230057872469803 * 10 ^ 70 +
        2288977332844599420283750836629176468381387502285944935758543098903132) * 10 ^ 70 +
        0371993113898250930563464310186308444923139822597509466690087111036300) : ℚ) := by
  unfold
    remainder7Coefficient1
    remainder7Coefficient1Block0
    remainder7Coefficient1Chunk10
    remainder7Coefficient1Chunk9
    remainder7Coefficient1Chunk8
    remainder7Coefficient1Chunk7
    remainder7Coefficient1Chunk6
    remainder7Coefficient1Chunk5
    remainder7Coefficient1Chunk4
    remainder7Coefficient1Chunk3
    remainder7Coefficient1Chunk2
    remainder7Coefficient1Chunk1
    remainder7Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C1_coeff_12 :
    remainder7Coefficient1.coeff 12 =
      -(((514268970614403235959990426406 * 10 ^ 70 +
        7323887834737051383148075909355844349926192501518934693328549639530298) * 10 ^ 70 +
        0823548183549009178708043512200602783929324580639575781122385356195000) : ℚ) := by
  unfold
    remainder7Coefficient1
    remainder7Coefficient1Block0
    remainder7Coefficient1Chunk10
    remainder7Coefficient1Chunk9
    remainder7Coefficient1Chunk8
    remainder7Coefficient1Chunk7
    remainder7Coefficient1Chunk6
    remainder7Coefficient1Chunk5
    remainder7Coefficient1Chunk4
    remainder7Coefficient1Chunk3
    remainder7Coefficient1Chunk2
    remainder7Coefficient1Chunk1
    remainder7Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C1_coeff_13 :
    remainder7Coefficient1.coeff 13 =
      (((11000523111860103180746238150738 * 10 ^ 70 +
        3696681390448056779453964512194873168528116092726079174664773349485418) * 10 ^ 70 +
        6357971241224339704517139470069582640615476937265097020213492210798000) : ℚ) := by
  unfold
    remainder7Coefficient1
    remainder7Coefficient1Block0
    remainder7Coefficient1Chunk10
    remainder7Coefficient1Chunk9
    remainder7Coefficient1Chunk8
    remainder7Coefficient1Chunk7
    remainder7Coefficient1Chunk6
    remainder7Coefficient1Chunk5
    remainder7Coefficient1Chunk4
    remainder7Coefficient1Chunk3
    remainder7Coefficient1Chunk2
    remainder7Coefficient1Chunk1
    remainder7Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C1_coeff_14 :
    remainder7Coefficient1.coeff 14 =
      -(((189728231166416778635321846297752 * 10 ^ 70 +
        0706907072664392277813797016010448929407335928575094165799349661567888) * 10 ^ 70 +
        5426284325723128568687449845461534211377270133341851925094998105730900) : ℚ) := by
  unfold
    remainder7Coefficient1
    remainder7Coefficient1Block0
    remainder7Coefficient1Chunk10
    remainder7Coefficient1Chunk9
    remainder7Coefficient1Chunk8
    remainder7Coefficient1Chunk7
    remainder7Coefficient1Chunk6
    remainder7Coefficient1Chunk5
    remainder7Coefficient1Chunk4
    remainder7Coefficient1Chunk3
    remainder7Coefficient1Chunk2
    remainder7Coefficient1Chunk1
    remainder7Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C1_coeff_15 :
    remainder7Coefficient1.coeff 15 =
      (((2675663671167821118618234682312190 * 10 ^ 70 +
        5716206634001397747390357189592803442700905226578587559303952242469318) * 10 ^ 70 +
        7695984220871596194341123932671721116591542808006385733670974618543500) : ℚ) := by
  unfold
    remainder7Coefficient1
    remainder7Coefficient1Block0
    remainder7Coefficient1Chunk10
    remainder7Coefficient1Chunk9
    remainder7Coefficient1Chunk8
    remainder7Coefficient1Chunk7
    remainder7Coefficient1Chunk6
    remainder7Coefficient1Chunk5
    remainder7Coefficient1Chunk4
    remainder7Coefficient1Chunk3
    remainder7Coefficient1Chunk2
    remainder7Coefficient1Chunk1
    remainder7Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C1_coeff_16 :
    remainder7Coefficient1.coeff 16 =
      -(((31243286546665870522320811607122574 * 10 ^ 70 +
        9611258879421509611402994670659931505163156950364114549515672649681148) * 10 ^ 70 +
        2424074298538289729756628289410669827243618294471311858233088999704800) : ℚ) := by
  unfold
    remainder7Coefficient1
    remainder7Coefficient1Block0
    remainder7Coefficient1Chunk10
    remainder7Coefficient1Chunk9
    remainder7Coefficient1Chunk8
    remainder7Coefficient1Chunk7
    remainder7Coefficient1Chunk6
    remainder7Coefficient1Chunk5
    remainder7Coefficient1Chunk4
    remainder7Coefficient1Chunk3
    remainder7Coefficient1Chunk2
    remainder7Coefficient1Chunk1
    remainder7Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C1_coeff_17 :
    remainder7Coefficient1.coeff 17 =
      (((305549767680281780756309122945637955 * 10 ^ 70 +
        5357452504705733692558444588541196115062898416921598966344309812118012) * 10 ^ 70 +
        0115057683414812713754326479968601591790337072675375978676539249087000) : ℚ) := by
  unfold
    remainder7Coefficient1
    remainder7Coefficient1Block0
    remainder7Coefficient1Chunk10
    remainder7Coefficient1Chunk9
    remainder7Coefficient1Chunk8
    remainder7Coefficient1Chunk7
    remainder7Coefficient1Chunk6
    remainder7Coefficient1Chunk5
    remainder7Coefficient1Chunk4
    remainder7Coefficient1Chunk3
    remainder7Coefficient1Chunk2
    remainder7Coefficient1Chunk1
    remainder7Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C1_coeff_18 :
    remainder7Coefficient1.coeff 18 =
      -(((2529401652115669509625093293591017235 * 10 ^ 70 +
        5423129450176131908446516446595559521580619912777861611315355702622050) * 10 ^ 70 +
        1004474801947547738358897149312764577332791168497214556606267949529100) : ℚ) := by
  unfold
    remainder7Coefficient1
    remainder7Coefficient1Block0
    remainder7Coefficient1Chunk10
    remainder7Coefficient1Chunk9
    remainder7Coefficient1Chunk8
    remainder7Coefficient1Chunk7
    remainder7Coefficient1Chunk6
    remainder7Coefficient1Chunk5
    remainder7Coefficient1Chunk4
    remainder7Coefficient1Chunk3
    remainder7Coefficient1Chunk2
    remainder7Coefficient1Chunk1
    remainder7Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C1_coeff_19 :
    remainder7Coefficient1.coeff 19 =
      (((17900885256329515831943276119469514881 * 10 ^ 70 +
        6147824933149978805769311994445102962915193965415628234093855154418970) * 10 ^ 70 +
        7397091104212339815604283847425888916657500258104675102344332478942100) : ℚ) := by
  unfold
    remainder7Coefficient1
    remainder7Coefficient1Block0
    remainder7Coefficient1Chunk10
    remainder7Coefficient1Chunk9
    remainder7Coefficient1Chunk8
    remainder7Coefficient1Chunk7
    remainder7Coefficient1Chunk6
    remainder7Coefficient1Chunk5
    remainder7Coefficient1Chunk4
    remainder7Coefficient1Chunk3
    remainder7Coefficient1Chunk2
    remainder7Coefficient1Chunk1
    remainder7Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C1_coeff_20 :
    remainder7Coefficient1.coeff 20 =
      -(((109319368313228189000348413043914382243 * 10 ^ 70 +
        2147176144478554290800314799357644864115881120174815940188430080891694) * 10 ^ 70 +
        0598393309335859841037493536606966358130876167861309312653803565256100) : ℚ) := by
  unfold
    remainder7Coefficient1
    remainder7Coefficient1Block0
    remainder7Coefficient1Chunk10
    remainder7Coefficient1Chunk9
    remainder7Coefficient1Chunk8
    remainder7Coefficient1Chunk7
    remainder7Coefficient1Chunk6
    remainder7Coefficient1Chunk5
    remainder7Coefficient1Chunk4
    remainder7Coefficient1Chunk3
    remainder7Coefficient1Chunk2
    remainder7Coefficient1Chunk1
    remainder7Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C1_coeff_21 :
    remainder7Coefficient1.coeff 21 =
      (((581139763781811068884305058217217238497 * 10 ^ 70 +
        1220815011541927728282067538764800621902110883784856237156030418817061) * 10 ^ 70 +
        9962489964992668137095065881450336991007712687881280573536806451516200) : ℚ) := by
  unfold
    remainder7Coefficient1
    remainder7Coefficient1Block0
    remainder7Coefficient1Chunk10
    remainder7Coefficient1Chunk9
    remainder7Coefficient1Chunk8
    remainder7Coefficient1Chunk7
    remainder7Coefficient1Chunk6
    remainder7Coefficient1Chunk5
    remainder7Coefficient1Chunk4
    remainder7Coefficient1Chunk3
    remainder7Coefficient1Chunk2
    remainder7Coefficient1Chunk1
    remainder7Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C1_coeff_22 :
    remainder7Coefficient1.coeff 22 =
      -(((2711254037058867852017477288639112678524 * 10 ^ 70 +
        5731648020254624555351110656320264175357198722775124201640213746930232) * 10 ^ 70 +
        9172833190757847390226110147632751785277368441387737629524351861471000) : ℚ) := by
  unfold
    remainder7Coefficient1
    remainder7Coefficient1Block0
    remainder7Coefficient1Chunk10
    remainder7Coefficient1Chunk9
    remainder7Coefficient1Chunk8
    remainder7Coefficient1Chunk7
    remainder7Coefficient1Chunk6
    remainder7Coefficient1Chunk5
    remainder7Coefficient1Chunk4
    remainder7Coefficient1Chunk3
    remainder7Coefficient1Chunk2
    remainder7Coefficient1Chunk1
    remainder7Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C1_coeff_23 :
    remainder7Coefficient1.coeff 23 =
      (((11185345497206780918869428255734827040187 * 10 ^ 70 +
        4829438842257650972777891062728087926871119396368124799244085326882372) * 10 ^ 70 +
        1773081680826917042495242564601194642732927045414322589867897306458600) : ℚ) := by
  unfold
    remainder7Coefficient1
    remainder7Coefficient1Block0
    remainder7Coefficient1Chunk10
    remainder7Coefficient1Chunk9
    remainder7Coefficient1Chunk8
    remainder7Coefficient1Chunk7
    remainder7Coefficient1Chunk6
    remainder7Coefficient1Chunk5
    remainder7Coefficient1Chunk4
    remainder7Coefficient1Chunk3
    remainder7Coefficient1Chunk2
    remainder7Coefficient1Chunk1
    remainder7Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C1_coeff_24 :
    remainder7Coefficient1.coeff 24 =
      -(((41088179284411376532531302301499658544816 * 10 ^ 70 +
        6402289064218705864810468816561129478727208928187717827783831170478107) * 10 ^ 70 +
        4541829444540613798747392628704474610461746015625476367947242758144500) : ℚ) := by
  unfold
    remainder7Coefficient1
    remainder7Coefficient1Block0
    remainder7Coefficient1Chunk10
    remainder7Coefficient1Chunk9
    remainder7Coefficient1Chunk8
    remainder7Coefficient1Chunk7
    remainder7Coefficient1Chunk6
    remainder7Coefficient1Chunk5
    remainder7Coefficient1Chunk4
    remainder7Coefficient1Chunk3
    remainder7Coefficient1Chunk2
    remainder7Coefficient1Chunk1
    remainder7Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C1_coeff_25 :
    remainder7Coefficient1.coeff 25 =
      (((135224661201581008763275693405257481811396 * 10 ^ 70 +
        7683259599166313913050928142595870439907424088703572026130395847937274) * 10 ^ 70 +
        8215236092740806433428470385074552256198216462382234533446795775708000) : ℚ) := by
  unfold
    remainder7Coefficient1
    remainder7Coefficient1Block0
    remainder7Coefficient1Chunk10
    remainder7Coefficient1Chunk9
    remainder7Coefficient1Chunk8
    remainder7Coefficient1Chunk7
    remainder7Coefficient1Chunk6
    remainder7Coefficient1Chunk5
    remainder7Coefficient1Chunk4
    remainder7Coefficient1Chunk3
    remainder7Coefficient1Chunk2
    remainder7Coefficient1Chunk1
    remainder7Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C1_coeff_26 :
    remainder7Coefficient1.coeff 26 =
      -(((400867228948276184196256815204853300816016 * 10 ^ 70 +
        4790611190249660624477692600404124310094096741149895815233583269322956) * 10 ^ 70 +
        4134202562875944250616373660372633588040454495530073580838721039851000) : ℚ) := by
  unfold
    remainder7Coefficient1
    remainder7Coefficient1Block0
    remainder7Coefficient1Chunk10
    remainder7Coefficient1Chunk9
    remainder7Coefficient1Chunk8
    remainder7Coefficient1Chunk7
    remainder7Coefficient1Chunk6
    remainder7Coefficient1Chunk5
    remainder7Coefficient1Chunk4
    remainder7Coefficient1Chunk3
    remainder7Coefficient1Chunk2
    remainder7Coefficient1Chunk1
    remainder7Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C1_coeff_27 :
    remainder7Coefficient1.coeff 27 =
      (((1075244597673637159774524643333283720499724 * 10 ^ 70 +
        8273529793308914531750459159023946280834586659031428080945125618675219) * 10 ^ 70 +
        7275243076552722501453316048776723012451562576694993682906554016753300) : ℚ) := by
  unfold
    remainder7Coefficient1
    remainder7Coefficient1Block0
    remainder7Coefficient1Chunk10
    remainder7Coefficient1Chunk9
    remainder7Coefficient1Chunk8
    remainder7Coefficient1Chunk7
    remainder7Coefficient1Chunk6
    remainder7Coefficient1Chunk5
    remainder7Coefficient1Chunk4
    remainder7Coefficient1Chunk3
    remainder7Coefficient1Chunk2
    remainder7Coefficient1Chunk1
    remainder7Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C1_coeff_28 :
    remainder7Coefficient1.coeff 28 =
      -(((2619023658909728040831322062001345142124021 * 10 ^ 70 +
        3760017857263700399561477785393029016922442965310629674690690462579010) * 10 ^ 70 +
        6530330327510673705839303345831916838299975311925277927045719561092000) : ℚ) := by
  unfold
    remainder7Coefficient1
    remainder7Coefficient1Block0
    remainder7Coefficient1Chunk10
    remainder7Coefficient1Chunk9
    remainder7Coefficient1Chunk8
    remainder7Coefficient1Chunk7
    remainder7Coefficient1Chunk6
    remainder7Coefficient1Chunk5
    remainder7Coefficient1Chunk4
    remainder7Coefficient1Chunk3
    remainder7Coefficient1Chunk2
    remainder7Coefficient1Chunk1
    remainder7Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C1_coeff_29 :
    remainder7Coefficient1.coeff 29 =
      (((5808603629938132456446368659778570937425706 * 10 ^ 70 +
        7322729870857736697026583339026245691309251555437977819345440566807881) * 10 ^ 70 +
        1582909019934256638638094361896232831268171360128451855114395949041300) : ℚ) := by
  unfold
    remainder7Coefficient1
    remainder7Coefficient1Block0
    remainder7Coefficient1Chunk10
    remainder7Coefficient1Chunk9
    remainder7Coefficient1Chunk8
    remainder7Coefficient1Chunk7
    remainder7Coefficient1Chunk6
    remainder7Coefficient1Chunk5
    remainder7Coefficient1Chunk4
    remainder7Coefficient1Chunk3
    remainder7Coefficient1Chunk2
    remainder7Coefficient1Chunk1
    remainder7Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C1_coeff_30 :
    remainder7Coefficient1.coeff 30 =
      -(((11752120546333417165533985502192354551418600 * 10 ^ 70 +
        0648355850985507647987940633746982725872756852720584061986758894124297) * 10 ^ 70 +
        6159005394581724190355852558129534742995239341899979741164660390250600) : ℚ) := by
  unfold
    remainder7Coefficient1
    remainder7Coefficient1Block0
    remainder7Coefficient1Chunk10
    remainder7Coefficient1Chunk9
    remainder7Coefficient1Chunk8
    remainder7Coefficient1Chunk7
    remainder7Coefficient1Chunk6
    remainder7Coefficient1Chunk5
    remainder7Coefficient1Chunk4
    remainder7Coefficient1Chunk3
    remainder7Coefficient1Chunk2
    remainder7Coefficient1Chunk1
    remainder7Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C1_coeff_31 :
    remainder7Coefficient1.coeff 31 =
      (((21715303464190810628156696376500916370290754 * 10 ^ 70 +
        9916045847009809308900129729598371963146444474022564713411546538602269) * 10 ^ 70 +
        4635066095340405896498744484334068109910346648378154548570196936506100) : ℚ) := by
  unfold
    remainder7Coefficient1
    remainder7Coefficient1Block0
    remainder7Coefficient1Chunk10
    remainder7Coefficient1Chunk9
    remainder7Coefficient1Chunk8
    remainder7Coefficient1Chunk7
    remainder7Coefficient1Chunk6
    remainder7Coefficient1Chunk5
    remainder7Coefficient1Chunk4
    remainder7Coefficient1Chunk3
    remainder7Coefficient1Chunk2
    remainder7Coefficient1Chunk1
    remainder7Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C1_coeff_32 :
    remainder7Coefficient1.coeff 32 =
      -(((36664706653791903445343340862064220219743520 * 10 ^ 70 +
        1458574778973224928701729054938451752204452819325062579851609362777510) * 10 ^ 70 +
        5018903631976367661523204828619863980435414288626526202138101909670800) : ℚ) := by
  unfold
    remainder7Coefficient1
    remainder7Coefficient1Block0
    remainder7Coefficient1Chunk10
    remainder7Coefficient1Chunk9
    remainder7Coefficient1Chunk8
    remainder7Coefficient1Chunk7
    remainder7Coefficient1Chunk6
    remainder7Coefficient1Chunk5
    remainder7Coefficient1Chunk4
    remainder7Coefficient1Chunk3
    remainder7Coefficient1Chunk2
    remainder7Coefficient1Chunk1
    remainder7Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C1_coeff_33 :
    remainder7Coefficient1.coeff 33 =
      (((56569040083718506639818572513182768047804167 * 10 ^ 70 +
        6873594500998550652758456514075564116013706518013713069838130625163635) * 10 ^ 70 +
        7294331932664725615335103467515950826228687781567274751459720839963500) : ℚ) := by
  unfold
    remainder7Coefficient1
    remainder7Coefficient1Block0
    remainder7Coefficient1Chunk10
    remainder7Coefficient1Chunk9
    remainder7Coefficient1Chunk8
    remainder7Coefficient1Chunk7
    remainder7Coefficient1Chunk6
    remainder7Coefficient1Chunk5
    remainder7Coefficient1Chunk4
    remainder7Coefficient1Chunk3
    remainder7Coefficient1Chunk2
    remainder7Coefficient1Chunk1
    remainder7Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C1_coeff_34 :
    remainder7Coefficient1.coeff 34 =
      -(((79727244954223011897759154219421855255114195 * 10 ^ 70 +
        7039105408847362302319554436950133571838529172740396814719319755054614) * 10 ^ 70 +
        4286180536156009364047299802309015618850843754211098148060330427324700) : ℚ) := by
  unfold
    remainder7Coefficient1
    remainder7Coefficient1Block0
    remainder7Coefficient1Chunk10
    remainder7Coefficient1Chunk9
    remainder7Coefficient1Chunk8
    remainder7Coefficient1Chunk7
    remainder7Coefficient1Chunk6
    remainder7Coefficient1Chunk5
    remainder7Coefficient1Chunk4
    remainder7Coefficient1Chunk3
    remainder7Coefficient1Chunk2
    remainder7Coefficient1Chunk1
    remainder7Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C1_coeff_35 :
    remainder7Coefficient1.coeff 35 =
      (((102575876680591497354449314111224497782555304 * 10 ^ 70 +
        4848625081909351305712240783309857027986267597154589062945994781688921) * 10 ^ 70 +
        9178078600542726679521870176677873799562165691410867733399921660771400) : ℚ) := by
  unfold
    remainder7Coefficient1
    remainder7Coefficient1Block0
    remainder7Coefficient1Chunk10
    remainder7Coefficient1Chunk9
    remainder7Coefficient1Chunk8
    remainder7Coefficient1Chunk7
    remainder7Coefficient1Chunk6
    remainder7Coefficient1Chunk5
    remainder7Coefficient1Chunk4
    remainder7Coefficient1Chunk3
    remainder7Coefficient1Chunk2
    remainder7Coefficient1Chunk1
    remainder7Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C1_coeff_36 :
    remainder7Coefficient1.coeff 36 =
      -(((120360381549769321769604300296928797227994994 * 10 ^ 70 +
        0002428582472779063898719934935455380779691003872638368201476393599996) * 10 ^ 70 +
        2240773546156566731708324753394860439836293602936183465072007089423500) : ℚ) := by
  unfold
    remainder7Coefficient1
    remainder7Coefficient1Block0
    remainder7Coefficient1Chunk10
    remainder7Coefficient1Chunk9
    remainder7Coefficient1Chunk8
    remainder7Coefficient1Chunk7
    remainder7Coefficient1Chunk6
    remainder7Coefficient1Chunk5
    remainder7Coefficient1Chunk4
    remainder7Coefficient1Chunk3
    remainder7Coefficient1Chunk2
    remainder7Coefficient1Chunk1
    remainder7Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C1_coeff_37 :
    remainder7Coefficient1.coeff 37 =
      (((128640267626845844871783284236179748061772226 * 10 ^ 70 +
        3380756762264449169137906116301333265791895369830921499187217096576088) * 10 ^ 70 +
        4746108405969082400083279410047531732811049771807439483777313506138700) : ℚ) := by
  unfold
    remainder7Coefficient1
    remainder7Coefficient1Block0
    remainder7Coefficient1Chunk10
    remainder7Coefficient1Chunk9
    remainder7Coefficient1Chunk8
    remainder7Coefficient1Chunk7
    remainder7Coefficient1Chunk6
    remainder7Coefficient1Chunk5
    remainder7Coefficient1Chunk4
    remainder7Coefficient1Chunk3
    remainder7Coefficient1Chunk2
    remainder7Coefficient1Chunk1
    remainder7Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C1_coeff_38 :
    remainder7Coefficient1.coeff 38 =
      -(((125028287630023308300164665233770601262709975 * 10 ^ 70 +
        5900780667029654942867594270034243815587757320984973257176731976667065) * 10 ^ 70 +
        3496697988865414494497167361016857095141427732166846452543317722129300) : ℚ) := by
  unfold
    remainder7Coefficient1
    remainder7Coefficient1Block0
    remainder7Coefficient1Chunk10
    remainder7Coefficient1Chunk9
    remainder7Coefficient1Chunk8
    remainder7Coefficient1Chunk7
    remainder7Coefficient1Chunk6
    remainder7Coefficient1Chunk5
    remainder7Coefficient1Chunk4
    remainder7Coefficient1Chunk3
    remainder7Coefficient1Chunk2
    remainder7Coefficient1Chunk1
    remainder7Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C1_coeff_39 :
    remainder7Coefficient1.coeff 39 =
      (((110257889718880697403840974611779357168791240 * 10 ^ 70 +
        8839938203799162046723580757217656953389989111517706422388198509931394) * 10 ^ 70 +
        2257400958683697401754387255810052506425013962986728966543407405533000) : ℚ) := by
  unfold
    remainder7Coefficient1
    remainder7Coefficient1Block0
    remainder7Coefficient1Chunk10
    remainder7Coefficient1Chunk9
    remainder7Coefficient1Chunk8
    remainder7Coefficient1Chunk7
    remainder7Coefficient1Chunk6
    remainder7Coefficient1Chunk5
    remainder7Coefficient1Chunk4
    remainder7Coefficient1Chunk3
    remainder7Coefficient1Chunk2
    remainder7Coefficient1Chunk1
    remainder7Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C1_coeff_40 :
    remainder7Coefficient1.coeff 40 =
      -(((87946235831429590751564519270494540286551781 * 10 ^ 70 +
        6194609437231668973206815811259602712154988478178496382088988641807529) * 10 ^ 70 +
        9022435137382301380153326311891775727096326737300978247307157055541900) : ℚ) := by
  unfold
    remainder7Coefficient1
    remainder7Coefficient1Block0
    remainder7Coefficient1Chunk10
    remainder7Coefficient1Chunk9
    remainder7Coefficient1Chunk8
    remainder7Coefficient1Chunk7
    remainder7Coefficient1Chunk6
    remainder7Coefficient1Chunk5
    remainder7Coefficient1Chunk4
    remainder7Coefficient1Chunk3
    remainder7Coefficient1Chunk2
    remainder7Coefficient1Chunk1
    remainder7Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C1_coeff_41 :
    remainder7Coefficient1.coeff 41 =
      (((63154269720438939736664879369597904815712612 * 10 ^ 70 +
        1818422083400786493448658639074019055418717405647721385417615725674009) * 10 ^ 70 +
        2240106883233865317906191976798698025751962964160181691143428140133700) : ℚ) := by
  unfold
    remainder7Coefficient1
    remainder7Coefficient1Block0
    remainder7Coefficient1Chunk10
    remainder7Coefficient1Chunk9
    remainder7Coefficient1Chunk8
    remainder7Coefficient1Chunk7
    remainder7Coefficient1Chunk6
    remainder7Coefficient1Chunk5
    remainder7Coefficient1Chunk4
    remainder7Coefficient1Chunk3
    remainder7Coefficient1Chunk2
    remainder7Coefficient1Chunk1
    remainder7Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5C1_coeff_42 :
    remainder7Coefficient1.coeff 42 =
      -(((40527667127888957120699419021654306711665225 * 10 ^ 70 +
        1880795752079586373075903647186739456560609948025876867404637025846901) * 10 ^ 70 +
        6619467480560273862619894634353371054772012594370590329904770781927500) : ℚ) := by
  unfold
    remainder7Coefficient1
    remainder7Coefficient1Block0
    remainder7Coefficient1Chunk10
    remainder7Coefficient1Chunk9
    remainder7Coefficient1Chunk8
    remainder7Coefficient1Chunk7
    remainder7Coefficient1Chunk6
    remainder7Coefficient1Chunk5
    remainder7Coefficient1Chunk4
    remainder7Coefficient1Chunk3
    remainder7Coefficient1Chunk2
    remainder7Coefficient1Chunk1
    remainder7Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
