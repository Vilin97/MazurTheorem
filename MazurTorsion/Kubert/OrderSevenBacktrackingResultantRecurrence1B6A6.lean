/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1SourceData
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1Remainder2Data
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1CommonData

import Mathlib.Tactic.Ring

/-!
# Recurrence 1 certificate: B6A6

This file is a checked bounded-band arithmetic shard for the first
pseudo-division recurrence in the order-seven branch-zero resultant certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

private def recurrence1B6A6Row0Band0 : Coefficient :=
  X ^ 0 * (
    (8484) * X ^ 1 +
    (3671682) * X ^ 2 +
    (-9209094566) * X ^ 3 +
    (642748213632) * X ^ 4 +
    (108543867251526) * X ^ 5 +
    (-3715824406928081) * X ^ 6 +
    (-237580706642134695) * X ^ 7 +
    (1715574246147851740) * X ^ 8
  )

private def recurrence1B6A6Row0Band1 : Coefficient :=
  X ^ 9 * (
    (207691546925597653086) +
    (980959202292051114300) * X ^ 1 +
    (-61213162839142393972956) * X ^ 2 +
    (-934312914601103094603868) * X ^ 3 +
    (8584708868275477562123912) * X ^ 4 +
    (189021514448919284507244744) * X ^ 5 +
    (143230723810704531403067148) * X ^ 6 +
    (-24296359055442623232696045069) * X ^ 7 +
    (-88579597633732793392886613014) * X ^ 8
  )

private def recurrence1B6A6Row0Band2 : Coefficient :=
  X ^ 18 * (
    (1574762679268093824533389602923) +
    (11997936874083945948003176748258) * X ^ 1 +
    (-77489877007264357426179360856794) * X ^ 2 +
    (-791143520035039796148012053551357) * X ^ 3 +
    (2487464873493264421105452307323378) * X ^ 4 +
    (38600402149119351950444371441778715) * X ^ 5 +
    (-67093791084112884598613425857314189) * X ^ 6 +
    (-1420615461355864573932865357137634877) * X ^ 7 +
    (1686561617655121304252072902781671714) * X ^ 8
  )

private def recurrence1B6A6Row0Band3 : Coefficient :=
  X ^ 27 * (
    (42396002131028183084541112526632162976) +
    (-50788610745832040295800696326456416953) * X ^ 1 +
    (-1037063646041962281726377014573411150118) * X ^ 2 +
    (1672530349452306226587690406298381587629) * X ^ 3 +
    (20700773552054671220854225326006398616023) * X ^ 4 +
    (-49401592481791494817992643793416621141297) * X ^ 5 +
    (-324076928178385517782619502260893156260882) * X ^ 6 +
    (1175725446199419393071174718533491860000331) * X ^ 7 +
    (3567149954365069330077352501779931384428815) * X ^ 8
  )

private def recurrence1B6A6Row0Band4 : Coefficient :=
  X ^ 36 * (
    (-21581638222522430968346367701685267099414998) +
    (-16483270108699398456514912132901375385009529) * X ^ 1 +
    (292512259484096477292236853943858233630457818) * X ^ 2 +
    (-285566325896070160539091142989187091090829745) * X ^ 3 +
    (-2650724372119177408244904615532729811950634481) * X ^ 4 +
    (7595609567355989347007701259603439582610580815) * X ^ 5 +
    (10539092610290863980817139953533801567194223570) * X ^ 6 +
    (-86162683909187069306090942413307990037333013505) * X ^ 7 +
    (86366103800273731444841359650615285916315319366) * X ^ 8
  )

private def recurrence1B6A6Row0Band5 : Coefficient :=
  X ^ 45 * (
    (470062718956366989427806146638920131582306396627) +
    (-1587582274617349013536644148895546229804380104967) * X ^ 1 +
    (355604343495187340969595309444914467082377490467) * X ^ 2 +
    (8750163879845297807331409659561983177198556686368) * X ^ 3 +
    (-21350615800223330916888353785691369203757595240188) * X ^ 4 +
    (3073353393915211561386851285603786637128082070161) * X ^ 5 +
    (93578358185974405264651646077519892777665396945035) * X ^ 6 +
    (-226292923614562575333478494405108025801311162703242) * X ^ 7 +
    (148227743911672832861683999325718278780151974086496) * X ^ 8
  )

private def recurrence1B6A6Row0Band6 : Coefficient :=
  X ^ 54 * (
    (468859465294201443527833257555215355284684660505240) +
    (-1532804951305445335321233617437064683664243478998688) * X ^ 1 +
    (2073079179070613260537167949149989170439461081829217) * X ^ 2 +
    (-672284154177655682855831279299747291737952405372994) * X ^ 3 +
    (-3037362222989593547609852929269531361918285187281511) * X ^ 4 +
    (7161961200628882459137478100052805570027057375717227) * X ^ 5 +
    (-8420845508880631039268589580946025595697820823459956) * X ^ 6 +
    (4968081267241012420446971437024434010049164940253358) * X ^ 7 +
    (1516408636212559699437743423638809380276164971279661) * X ^ 8
  )

private def recurrence1B6A6Row0Band7 : Coefficient :=
  X ^ 63 * (
    (-6919400896601197974073248666092316792830382088767620) +
    (8126365700980417900809930804055636371460433296697099) * X ^ 1 +
    (-5377949548553618869973172029161125850846898157042952) * X ^ 2 +
    (1430397472176857274929991404348329954235420541870843) * X ^ 3 +
    (1141131510286503954329882088832401108929371515853785) * X ^ 4 +
    (-1671998609477513844156633630114815997063746627359049) * X ^ 5 +
    (1037269092999461797417222234380957111938090361249279) * X ^ 6 +
    (-311148834273666961625179375373581409058763043816597) * X ^ 7 +
    (-41772328228868440582078964452237175011164580429184) * X ^ 8
  )

private def recurrence1B6A6Row0Band8 : Coefficient :=
  X ^ 72 * (
    (92157701578416064868942053948860311256460161934756) +
    (-44396458011961923716236124677088666808302430492473) * X ^ 1 +
    (8373429434236474285125365031233966258654636076823) * X ^ 2 +
    (1872747660432245306882554041455604400185552840532) * X ^ 3 +
    (-1586091520374060331270488666655052455133509654527) * X ^ 4 +
    (359347225624504811742856092962327342956636254890) * X ^ 5 +
    (12871088362724762657767381362172211864731796524) * X ^ 6 +
    (-23859830266861621048181585708811951830499526884) * X ^ 7 +
    (3794593982886724534649159119939231281744806182) * X ^ 8
  )

private def recurrence1B6A6Row0Band9 : Coefficient :=
  X ^ 81 * (
    (371212006316039779670170528180506877406092520) +
    (-152691443512804633703894434097619355823499137) * X ^ 1 +
    (638522289861569532962416567634933428275826) * X ^ 2 +
    (2821437193165894413665454239658011593293835) * X ^ 3 +
    (16452997271719386350977635342887214240943) * X ^ 4 +
    (-29293349807443056479108138832452983871935) * X ^ 5 +
    (-2279884972382547172805080410601096736882) * X ^ 6 +
    (-74284238390018007323008569290067019283) * X ^ 7 +
    (-1209048704973416601808452595554131507) * X ^ 8
  )

private def recurrence1B6A6Row0Band10 : Coefficient :=
  X ^ 90 * (
    (-9969340216355267902600652130301545) +
    (-38075161201267936972537803474661) * X ^ 1 +
    (-38919488432148559395123725083) * X ^ 2 +
    (114882301852028897426662191) * X ^ 3 +
    (252869532458851314665610) * X ^ 4 +
    (108244568568157320194) * X ^ 5 +
    (6979583924037704) * X ^ 6 +
    (22035699826) * X ^ 7 +
    (35) * X ^ 8
  )

private def recurrence1B6A6Row0 : Coefficient :=
  recurrence1B6A6Row0Band0 +
  recurrence1B6A6Row0Band1 +
  recurrence1B6A6Row0Band2 +
  recurrence1B6A6Row0Band3 +
  recurrence1B6A6Row0Band4 +
  recurrence1B6A6Row0Band5 +
  recurrence1B6A6Row0Band6 +
  recurrence1B6A6Row0Band7 +
  recurrence1B6A6Row0Band8 +
  recurrence1B6A6Row0Band9 +
  recurrence1B6A6Row0Band10

private theorem recurrence1B6A6Row0_eq :
    recurrence1Source6Block0 * recurrence1Remainder26 =
      recurrence1B6A6Row0 := by
  unfold recurrence1Source6Block0 recurrence1Remainder26 recurrence1Remainder26Block0
  unfold recurrence1Remainder26Block1 recurrence1Remainder26Block2 recurrence1Remainder26Block3
  unfold recurrence1Remainder26Block4 recurrence1Remainder26Block5 recurrence1Remainder26Block6
  unfold recurrence1Remainder26Block7 recurrence1Remainder26Block8 recurrence1Remainder26Block9
  unfold recurrence1Remainder26Block10 recurrence1B6A6Row0 recurrence1B6A6Row0Band0
  unfold recurrence1B6A6Row0Band1 recurrence1B6A6Row0Band2 recurrence1B6A6Row0Band3
  unfold recurrence1B6A6Row0Band4 recurrence1B6A6Row0Band5 recurrence1B6A6Row0Band6
  unfold recurrence1B6A6Row0Band7 recurrence1B6A6Row0Band8 recurrence1B6A6Row0Band9
  unfold recurrence1B6A6Row0Band10
  ring

private def recurrence1B6A6Band0 : Coefficient :=
  recurrence1B6A6Row0Band0

private theorem recurrence1B6A6Band0_eq :
    recurrence1B6A6Band0 = recurrence1B6A6Block0 := by
  unfold recurrence1B6A6Band0 recurrence1B6A6Row0Band0 recurrence1B6A6Block0
  ring

private def recurrence1B6A6Band1 : Coefficient :=
  recurrence1B6A6Row0Band1

private theorem recurrence1B6A6Band1_eq :
    recurrence1B6A6Band1 = recurrence1B6A6Block1 := by
  unfold recurrence1B6A6Band1 recurrence1B6A6Row0Band1 recurrence1B6A6Block1
  ring

private def recurrence1B6A6Band2 : Coefficient :=
  recurrence1B6A6Row0Band2

private theorem recurrence1B6A6Band2_eq :
    recurrence1B6A6Band2 = recurrence1B6A6Block2 := by
  unfold recurrence1B6A6Band2 recurrence1B6A6Row0Band2 recurrence1B6A6Block2
  ring

private def recurrence1B6A6Band3 : Coefficient :=
  recurrence1B6A6Row0Band3

private theorem recurrence1B6A6Band3_eq :
    recurrence1B6A6Band3 = recurrence1B6A6Block3 := by
  unfold recurrence1B6A6Band3 recurrence1B6A6Row0Band3 recurrence1B6A6Block3
  ring

private def recurrence1B6A6Band4 : Coefficient :=
  recurrence1B6A6Row0Band4

private theorem recurrence1B6A6Band4_eq :
    recurrence1B6A6Band4 = recurrence1B6A6Block4 := by
  unfold recurrence1B6A6Band4 recurrence1B6A6Row0Band4 recurrence1B6A6Block4
  ring

private def recurrence1B6A6Band5 : Coefficient :=
  recurrence1B6A6Row0Band5

private theorem recurrence1B6A6Band5_eq :
    recurrence1B6A6Band5 = recurrence1B6A6Block5 := by
  unfold recurrence1B6A6Band5 recurrence1B6A6Row0Band5 recurrence1B6A6Block5
  ring

private def recurrence1B6A6Band6 : Coefficient :=
  recurrence1B6A6Row0Band6

private theorem recurrence1B6A6Band6_eq :
    recurrence1B6A6Band6 = recurrence1B6A6Block6 := by
  unfold recurrence1B6A6Band6 recurrence1B6A6Row0Band6 recurrence1B6A6Block6
  ring

private def recurrence1B6A6Band7 : Coefficient :=
  recurrence1B6A6Row0Band7

private theorem recurrence1B6A6Band7_eq :
    recurrence1B6A6Band7 = recurrence1B6A6Block7 := by
  unfold recurrence1B6A6Band7 recurrence1B6A6Row0Band7 recurrence1B6A6Block7
  ring

private def recurrence1B6A6Band8 : Coefficient :=
  recurrence1B6A6Row0Band8

private theorem recurrence1B6A6Band8_eq :
    recurrence1B6A6Band8 = recurrence1B6A6Block8 := by
  unfold recurrence1B6A6Band8 recurrence1B6A6Row0Band8 recurrence1B6A6Block8
  ring

private def recurrence1B6A6Band9 : Coefficient :=
  recurrence1B6A6Row0Band9

private theorem recurrence1B6A6Band9_eq :
    recurrence1B6A6Band9 = recurrence1B6A6Block9 := by
  unfold recurrence1B6A6Band9 recurrence1B6A6Row0Band9 recurrence1B6A6Block9
  ring

private def recurrence1B6A6Band10 : Coefficient :=
  recurrence1B6A6Row0Band10

private theorem recurrence1B6A6Band10_eq :
    recurrence1B6A6Band10 = recurrence1B6A6Block10 := by
  unfold recurrence1B6A6Band10 recurrence1B6A6Row0Band10 recurrence1B6A6Block10
  ring

private def recurrence1B6A6Rows : Coefficient :=
  recurrence1B6A6Row0

private def recurrence1B6A6Bands : Coefficient :=
  recurrence1B6A6Band0 +
  recurrence1B6A6Band1 +
  recurrence1B6A6Band2 +
  recurrence1B6A6Band3 +
  recurrence1B6A6Band4 +
  recurrence1B6A6Band5 +
  recurrence1B6A6Band6 +
  recurrence1B6A6Band7 +
  recurrence1B6A6Band8 +
  recurrence1B6A6Band9 +
  recurrence1B6A6Band10

theorem recurrence1B6A6_eq :
    recurrence1Source6 * recurrence1Remainder26 =
      recurrence1B6A6 := by
  have rows :
      recurrence1Source6 * recurrence1Remainder26 =
        recurrence1B6A6Rows := by
    unfold recurrence1Source6 recurrence1B6A6Rows
    exact recurrence1B6A6Row0_eq
  rw [rows]
  have rearrange : recurrence1B6A6Rows = recurrence1B6A6Bands := by
    unfold recurrence1B6A6Rows recurrence1B6A6Bands recurrence1B6A6Row0 recurrence1B6A6Band0
    unfold recurrence1B6A6Band1 recurrence1B6A6Band2 recurrence1B6A6Band3 recurrence1B6A6Band4
    unfold recurrence1B6A6Band5 recurrence1B6A6Band6 recurrence1B6A6Band7 recurrence1B6A6Band8
    unfold recurrence1B6A6Band9 recurrence1B6A6Band10
    ring
  rw [rearrange]
  unfold recurrence1B6A6Bands recurrence1B6A6
  rw [recurrence1B6A6Band0_eq]
  rw [recurrence1B6A6Band1_eq]
  rw [recurrence1B6A6Band2_eq]
  rw [recurrence1B6A6Band3_eq]
  rw [recurrence1B6A6Band4_eq]
  rw [recurrence1B6A6Band5_eq]
  rw [recurrence1B6A6Band6_eq]
  rw [recurrence1B6A6Band7_eq]
  rw [recurrence1B6A6Band8_eq]
  rw [recurrence1B6A6Band9_eq]
  rw [recurrence1B6A6Band10_eq]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
