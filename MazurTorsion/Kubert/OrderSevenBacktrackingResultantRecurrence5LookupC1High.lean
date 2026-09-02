/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData5
import Mathlib.Tactic.NormNum

/-!
# Recurrence 5 lookup certificate: C1 source coefficients, high half

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence5C1_coeff_43 :
    remainder7Coefficient1.coeff 43 =
      (((22948700224895752897812162552978993405721142 * 10 ^ 70 +
        8281049533391460951549605363626293241617044267208013646713799440743340) * 10 ^ 70 +
        8125119871656720933449279168642830526380029562123949070501520598560100) : ℚ) := by
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

theorem recurrence5C1_coeff_44 :
    remainder7Coefficient1.coeff 44 =
      -(((11192822001415636529216414832950410904926956 * 10 ^ 70 +
        5744721567793213541722427054510578729503236702973635872888841104085271) * 10 ^ 70 +
        3883423669848813920297646815323631660903634829717266049019547654851800) : ℚ) := by
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

theorem recurrence5C1_coeff_45 :
    remainder7Coefficient1.coeff 45 =
      (((4453144331861630134812905698597264506034810 * 10 ^ 70 +
        6931655746470330092039965800989466715731687611319075903762286095445583) * 10 ^ 70 +
        5720357016379219850983148619907177142087557905143254167661657798142200) : ℚ) := by
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

theorem recurrence5C1_coeff_46 :
    remainder7Coefficient1.coeff 46 =
      -(((1216527662604188070751181685247660721185105 * 10 ^ 70 +
        8272151039117590680406315818415245260299104664795316688300220382014694) * 10 ^ 70 +
        6787569899900977543505210410672847057093739150420340114921010663371600) : ℚ) := by
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

theorem recurrence5C1_coeff_47 :
    remainder7Coefficient1.coeff 47 =
      (((568697607131425414861674621159144227099 * 10 ^ 70 +
        5343408980689121185110882854528869237785677646642839848075284698891965) * 10 ^ 70 +
        9688728976028758992454430153786376688233347453398558568873047781917700) : ℚ) := by
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

theorem recurrence5C1_coeff_48 :
    remainder7Coefficient1.coeff 48 =
      (((270648949861364995579733118819001358547234 * 10 ^ 70 +
        1663277164914020583078732806681158571425031766156285270754911081055839) * 10 ^ 70 +
        8331259477775334849709506495921912032497785052153411697951681180039200) : ℚ) := by
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

theorem recurrence5C1_coeff_49 :
    remainder7Coefficient1.coeff 49 =
      -(((214264252797151037464151023781753151191645 * 10 ^ 70 +
        0974908249327346449096908181594591477522871742414413374066827715039566) * 10 ^ 70 +
        7147521525337795562670168540888205830214277186241585943410163990231800) : ℚ) := by
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

theorem recurrence5C1_coeff_50 :
    remainder7Coefficient1.coeff 50 =
      (((106503310495420535981040548699811333753175 * 10 ^ 70 +
        2143680712107288079005454423388634966437953910657881166622462470644398) * 10 ^ 70 +
        8569258808852838012976217752530706105313078661119451923880393707003000) : ℚ) := by
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

theorem recurrence5C1_coeff_51 :
    remainder7Coefficient1.coeff 51 =
      -(((32579495607866689727648814429797970894775 * 10 ^ 70 +
        3654524265586656817193659520523252960219638500761817662479378685633393) * 10 ^ 70 +
        3467648665791350397464459932863604061217480589473349004652441716362600) : ℚ) := by
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

theorem recurrence5C1_coeff_52 :
    remainder7Coefficient1.coeff 52 =
      -(((2148967683619916614790242959875577592803 * 10 ^ 70 +
        0273906581425030656764630823484209281651229869163224699391481339394552) * 10 ^ 70 +
        6950424645862484654100351296272938697768696690551072934284420017214100) : ℚ) := by
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

theorem recurrence5C1_coeff_53 :
    remainder7Coefficient1.coeff 53 =
      (((12792100722825580674540212417511088263212 * 10 ^ 70 +
        8353028543580073062542775551659270063916927198226717857156493989335834) * 10 ^ 70 +
        3893494931743162697061097658409648422472274001322964842439413342382300) : ℚ) := by
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

theorem recurrence5C1_coeff_54 :
    remainder7Coefficient1.coeff 54 =
      -(((12617800992366866575110209471258316828485 * 10 ^ 70 +
        8257883464934667091412530853156953678100007687062478414435200924111252) * 10 ^ 70 +
        4511710495679055492222370336816420355853381183777230750770832750196500) : ℚ) := by
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

theorem recurrence5C1_coeff_55 :
    remainder7Coefficient1.coeff 55 =
      (((9023368342336084823122561131922849315082 * 10 ^ 70 +
        9671898420722675633290958080619901216667932148744992892774099313671343) * 10 ^ 70 +
        1531398434523574217431884062675608050703222586617200948515388691024000) : ℚ) := by
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

theorem recurrence5C1_coeff_56 :
    remainder7Coefficient1.coeff 56 =
      -(((5252696200216785658101930215629490469427 * 10 ^ 70 +
        4295002404763358402602009560033947376734948541318153624442136176796544) * 10 ^ 70 +
        4937386083610755812521138306127808015984100084671664006917366857610400) : ℚ) := by
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

theorem recurrence5C1_coeff_57 :
    remainder7Coefficient1.coeff 57 =
      (((2433431046918844581875833619447580313999 * 10 ^ 70 +
        6728777598992604362889685483478674486386748383531627885837165891276565) * 10 ^ 70 +
        3669116105924316662943499650177738492327668795719744891828604863153100) : ℚ) := by
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

theorem recurrence5C1_coeff_58 :
    remainder7Coefficient1.coeff 58 =
      -(((739270561986197042010900866620019397964 * 10 ^ 70 +
        8786881854932506012772144020443383923493055727507016138245416777223845) * 10 ^ 70 +
        9282256208311159056484509926152738006063389009950044097610323164111800) : ℚ) := by
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

theorem recurrence5C1_coeff_59 :
    remainder7Coefficient1.coeff 59 =
      -(((57584516490879684600642901893742119482 * 10 ^ 70 +
        1983324582686151605042658218270875474359032324754636557550885934711988) * 10 ^ 70 +
        3190084413520618777849802570581388817168492908464197768047682555449500) : ℚ) := by
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

theorem recurrence5C1_coeff_60 :
    remainder7Coefficient1.coeff 60 =
      (((297901598911640569497358929741140915751 * 10 ^ 70 +
        1829208748224648030917292971917977008642438007963833175887100684939010) * 10 ^ 70 +
        0521410279267787794429407610436783408132845340721246575870976511218700) : ℚ) := by
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

theorem recurrence5C1_coeff_61 :
    remainder7Coefficient1.coeff 61 =
      -(((276164442022567087915573211685029318024 * 10 ^ 70 +
        9780904094841291814983659354569461270271090484870423504538079100904931) * 10 ^ 70 +
        0007135428647083232146743751608914070022041021638383057118641979155200) : ℚ) := by
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

theorem recurrence5C1_coeff_62 :
    remainder7Coefficient1.coeff 62 =
      (((179012224830043500332170306658742653062 * 10 ^ 70 +
        3430204073044711185044967610028405948635483291513066322911896566908420) * 10 ^ 70 +
        7113788515737074706280270213305221592438685636537468080744119283349300) : ℚ) := by
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

theorem recurrence5C1_coeff_63 :
    remainder7Coefficient1.coeff 63 =
      -(((92571935703575347598027931898242414755 * 10 ^ 70 +
        1565823673636446588467976394319413806605398625298336906403615428783537) * 10 ^ 70 +
        9605642046868524395536531530936625828710199027202924826088224562068700) : ℚ) := by
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

theorem recurrence5C1_coeff_64 :
    remainder7Coefficient1.coeff 64 =
      (((39270150261353942076464510156722104530 * 10 ^ 70 +
        3676144598707213201046421488827602950920347683303802716816338167183544) * 10 ^ 70 +
        4842207666499310955769394970426033663057392253174193085100490101005400) : ℚ) := by
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

theorem recurrence5C1_coeff_65 :
    remainder7Coefficient1.coeff 65 =
      -(((13491697565877784939977391301650653418 * 10 ^ 70 +
        4822959098711241484319645742491619058066262202051154876752312840169137) * 10 ^ 70 +
        1643379114140297667800552546046678609254002407191899723801367176851600) : ℚ) := by
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

theorem recurrence5C1_coeff_66 :
    remainder7Coefficient1.coeff 66 =
      (((3541154840652002010211409021898100962 * 10 ^ 70 +
        1959030915173152187826146543733079361079633355095548641817605533575284) * 10 ^ 70 +
        3409695753981841274903270347011593775245931115141148087754048411593300) : ℚ) := by
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

theorem recurrence5C1_coeff_67 :
    remainder7Coefficient1.coeff 67 =
      -(((581468838389986202849374863145259680 * 10 ^ 70 +
        0172121499034244687547245176984151540556741137135865207562083237997124) * 10 ^ 70 +
        5995162941461877428140626874192378303877373021762873805941457024175000) : ℚ) := by
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

theorem recurrence5C1_coeff_68 :
    remainder7Coefficient1.coeff 68 =
      -(((13024800792658364230577347628817235 * 10 ^ 70 +
        5597203587946832332114229807143430502362538348757519669976119169982257) * 10 ^ 70 +
        5664520427386626587546177197927529327791730415188507681509815413117400) : ℚ) := by
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

theorem recurrence5C1_coeff_69 :
    remainder7Coefficient1.coeff 69 =
      (((44960332463232073858045994879056963 * 10 ^ 70 +
        2312558706350933937239091797652403515082347547243568411213221048728095) * 10 ^ 70 +
        9770470137631593768879047259204466502270544227314323336158573632211800) : ℚ) := by
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

theorem recurrence5C1_coeff_70 :
    remainder7Coefficient1.coeff 70 =
      -(((15615073939350596412885593046768822 * 10 ^ 70 +
        0736853449088973982169547555672286844075724436704541631889309442867443) * 10 ^ 70 +
        5706422889733511252564211798992353128638909759036489822284858794373500) : ℚ) := by
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

theorem recurrence5C1_coeff_71 :
    remainder7Coefficient1.coeff 71 =
      (((2839372928039447085071583485430671 * 10 ^ 70 +
        2389145195939019148978358658778064232572195940271787390384795686198725) * 10 ^ 70 +
        0871897886529749370476285864385821982115862761183974517125440442909000) : ℚ) := by
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

theorem recurrence5C1_coeff_72 :
    remainder7Coefficient1.coeff 72 =
      -(((196031547418487019301280344268748 * 10 ^ 70 +
        4898938542013506410722000227658407557494685369584434438090702036791668) * 10 ^ 70 +
        8939878077439641625698831286726744145459342768529214119508121518848900) : ℚ) := by
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

theorem recurrence5C1_coeff_73 :
    remainder7Coefficient1.coeff 73 =
      -(((28137289585015828297866172147814 * 10 ^ 70 +
        9564008994804517176723453687361615785962347948032866642317987605334108) * 10 ^ 70 +
        1376137088719197275263510980570880645174736396929316179298393427828700) : ℚ) := by
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

theorem recurrence5C1_coeff_74 :
    remainder7Coefficient1.coeff 74 =
      (((5863781691379942341999221661522 * 10 ^ 70 +
        5325712252503746296831150063032974424177590079242582562269623790488626) * 10 ^ 70 +
        1091298682345393746695876510418219651450643277965900486713096730211900) : ℚ) := by
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

theorem recurrence5C1_coeff_75 :
    remainder7Coefficient1.coeff 75 =
      (((52759079543464564982824513172 * 10 ^ 70 +
        4430585771284651525971842194128072519461171186386362338901505856319110) * 10 ^ 70 +
        5597030225629582344415283619165430875452185778810422751190000611143900) : ℚ) := by
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

theorem recurrence5C1_coeff_76 :
    remainder7Coefficient1.coeff 76 =
      (((22915023704505740582340084672 * 10 ^ 70 +
        7255431443498988272077084083460695817211232445637897907528127594484820) * 10 ^ 70 +
        9426889844908522396822645350477119553229534607911881472297892775510100) : ℚ) := by
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

theorem recurrence5C1_coeff_77 :
    remainder7Coefficient1.coeff 77 =
      -(((41222692124161852716003833805 * 10 ^ 70 +
        5073056427052123305778360574409674284210061097451354131182315586130827) * 10 ^ 70 +
        0417280421924340172521678983779765974955609268001576889000008407383800) : ℚ) := by
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

theorem recurrence5C1_coeff_78 :
    remainder7Coefficient1.coeff 78 =
      (((5948098336751310133480162309 * 10 ^ 70 +
        7785609360326957238262151397721218972921769184032583106519300107012084) * 10 ^ 70 +
        5713464665313814900543573837886835344168255895330256569709623531487200) : ℚ) := by
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

theorem recurrence5C1_coeff_79 :
    remainder7Coefficient1.coeff 79 =
      -(((91437796395587400670068030 * 10 ^ 70 +
        1159354094624288687351202527354439227791874338974287116892887478066078) * 10 ^ 70 +
        8741143594400915748924611365860599345772752935927416709026844178582900) : ℚ) := by
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

theorem recurrence5C1_coeff_80 :
    remainder7Coefficient1.coeff 80 =
      -(((204410399801499921251236 * 10 ^ 70 +
        2907712226676399258935771692685111153139819537678305098350085576839023) * 10 ^ 70 +
        3686145499360475302012473650084958151372301787260484176507074667881600) : ℚ) := by
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

theorem recurrence5C1_coeff_81 :
    remainder7Coefficient1.coeff 81 =
      (((1162688004743772551651 * 10 ^ 70 +
        9352434502618970629469796268851119839746199853695265750543506391089675) * 10 ^ 70 +
        0653950205064112726142496451834150330278233961510711826164261299800100) : ℚ) := by
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

theorem recurrence5C1_coeff_82 :
    remainder7Coefficient1.coeff 82 =
      -(((960451307658617730 * 10 ^ 70 +
        0192724922250766502112559763614125346516685408308162666908324775622327) * 10 ^ 70 +
        4906464831638794763241496494449450552020204643118340885969404002388200) : ℚ) := by
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

theorem recurrence5C1_coeff_83 :
    remainder7Coefficient1.coeff 83 =
      (((40799686439745 * 10 ^ 70 +
        7868262911100363202977002142544359613215016665324437636648105276638822) * 10 ^ 70 +
        5921348855795201580778828400696548459158347483472964714770385616697300) : ℚ) := by
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

theorem recurrence5C1_coeff_84 :
    remainder7Coefficient1.coeff 84 =
      -(((15574111 * 10 ^ 70 +
        9722266126802536741383677787954208286338905633087667473952093831708316) * 10 ^ 70 +
        2921568205678358405098446864079426408781113703694420237088677512308100) : ℚ) := by
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
