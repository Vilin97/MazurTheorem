/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData5
import Mathlib.Tactic.NormNum

/-!
# Recurrence 5 lookup certificate: C0 source coefficients, high half

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence5C0_coeff_45 :
    remainder7Coefficient0.coeff 45 =
      (((299216319995934435925003618516585357981123498 * 10 ^ 70 +
        6811672939790032310212632978540189535299913307672002487816957679682893) * 10 ^ 70 +
        9878201698464192341875767949401194618130465210053324628640518141093800) : ℚ) := by
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

theorem recurrence5C0_coeff_46 :
    remainder7Coefficient0.coeff 46 =
      -(((167379318465759567086372557667630211074737758 * 10 ^ 70 +
        9791387508073864454885617547688676950570390907836431765487923413844118) * 10 ^ 70 +
        3389905771624271938278336779563419635003316002588002913488700184283900) : ℚ) := by
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

theorem recurrence5C0_coeff_47 :
    remainder7Coefficient0.coeff 47 =
      (((82802897070280529040724718141089545704414818 * 10 ^ 70 +
        3809203324104021674793638081713660214335002434211289552413447610559929) * 10 ^ 70 +
        8183085602950358180417107149840757069477896220270044834125720347797400) : ℚ) := by
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

theorem recurrence5C0_coeff_48 :
    remainder7Coefficient0.coeff 48 =
      -(((35163661406667961304884785817600637448968244 * 10 ^ 70 +
        3029646140386876211995307106107439360689710769610891532550937215574707) * 10 ^ 70 +
        5223045307657141565419802456910558942597285810494727802038956693652000) : ℚ) := by
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

theorem recurrence5C0_coeff_49 :
    remainder7Coefficient0.coeff 49 =
      (((11949456545612271069056122320190369183214660 * 10 ^ 70 +
        5774121331368364335364425470311118175298287772908210796905840113890203) * 10 ^ 70 +
        7503100621629798582240077951829039349523244146848372669547921036158700) : ℚ) := by
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

theorem recurrence5C0_coeff_50 :
    remainder7Coefficient0.coeff 50 =
      -(((2518019641233534069676373089106191142771972 * 10 ^ 70 +
        5185605499524598615340389147870375366700046766973856438324866314832129) * 10 ^ 70 +
        7773175700025108301088942084883132883257935729068847062301381855863200) : ℚ) := by
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

theorem recurrence5C0_coeff_51 :
    remainder7Coefficient0.coeff 51 =
      -(((360602202850647375465124148581123422110034 * 10 ^ 70 +
        7658729991087813810881153001301155310543181501427908874819710642750816) * 10 ^ 70 +
        4131997940737449516230759015144734716650300925065684251387828117430300) : ℚ) := by
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

theorem recurrence5C0_coeff_52 :
    remainder7Coefficient0.coeff 52 =
      (((737328762161682688248893420782040622202699 * 10 ^ 70 +
        8952803049625106028093041346070803558265137438312109298872685665563323) * 10 ^ 70 +
        0536392397143934091052502421345008144522560414696110411588742260299900) : ℚ) := by
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

theorem recurrence5C0_coeff_53 :
    remainder7Coefficient0.coeff 53 =
      -(((465690278722343877685358238697594902042660 * 10 ^ 70 +
        0687388323304117057368660917922017512977349393695776914553954538386818) * 10 ^ 70 +
        7533762444618505758977156616470496361067539513805532575786933331390100) : ℚ) := by
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

theorem recurrence5C0_coeff_54 :
    remainder7Coefficient0.coeff 54 =
      (((193000455234211694250461692806540316175518 * 10 ^ 70 +
        0316292999357417611085114281580836605060397300173625273498543953169893) * 10 ^ 70 +
        8784009166065585985966196512808799196555527288060521552779333901494600) : ℚ) := by
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

theorem recurrence5C0_coeff_55 :
    remainder7Coefficient0.coeff 55 =
      -(((45489183151752191752346519041430743890101 * 10 ^ 70 +
        4665452674663995569587177951157421747938056251083786321905923358680861) * 10 ^ 70 +
        6000742871586416599132600025051508967138008592727572273096690832966800) : ℚ) := by
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

theorem recurrence5C0_coeff_56 :
    remainder7Coefficient0.coeff 56 =
      -(((9865098188415408972871554774085380880276 * 10 ^ 70 +
        8276043976610924202926831721313967582854161606977827437293056992914891) * 10 ^ 70 +
        3035623483666843925741078214215520099719841731248237032635247103615500) : ℚ) := by
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

theorem recurrence5C0_coeff_57 :
    remainder7Coefficient0.coeff 57 =
      (((21705449740189662314493746367775104903176 * 10 ^ 70 +
        8091344493531861601029971129317284863695248798307946075557965431955464) * 10 ^ 70 +
        7966172143674587237955068705703194974351248373583301078997341433088700) : ℚ) := by
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

theorem recurrence5C0_coeff_58 :
    remainder7Coefficient0.coeff 58 =
      -(((18981771659769225282048495550338448083101 * 10 ^ 70 +
        0031478298025092123378788167733264085852264910018885643361539607749953) * 10 ^ 70 +
        6885051653368836353653261459111917985490586162202531644711314449048700) : ℚ) := by
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

theorem recurrence5C0_coeff_59 :
    remainder7Coefficient0.coeff 59 =
      (((13557315518886969851270252430668246594332 * 10 ^ 70 +
        0691132285605044158591918978742420395247798754059383330379135232229750) * 10 ^ 70 +
        9872705462834546600280432829151993778410840913100086840594584961513100) : ℚ) := by
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

theorem recurrence5C0_coeff_60 :
    remainder7Coefficient0.coeff 60 =
      -(((8861136362341469306255974361565195378834 * 10 ^ 70 +
        5166797563124041182394873038304655127427325171054004532351589540124988) * 10 ^ 70 +
        3658906841358641226791923091515607132821488720121066076356492321311300) : ℚ) := by
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

theorem recurrence5C0_coeff_61 :
    remainder7Coefficient0.coeff 61 =
      (((5414826848425349309103566999050054244074 * 10 ^ 70 +
        0893264801282049249915546199124019915021918803325513118936732263257917) * 10 ^ 70 +
        8444164141019239142289446645486501535676377961187877489986173093799300) : ℚ) := by
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

theorem recurrence5C0_coeff_62 :
    remainder7Coefficient0.coeff 62 =
      -(((3065114515082650692917572527895564183513 * 10 ^ 70 +
        3898519529744000396575549796981404911235998064803338550317268444406709) * 10 ^ 70 +
        6875948042646842002857847267994759337780757031205678762830072117161700) : ℚ) := by
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

theorem recurrence5C0_coeff_63 :
    remainder7Coefficient0.coeff 63 =
      (((1576929229338252800596971686011781513955 * 10 ^ 70 +
        4023750470013581286536434065673507944217417163867312763986873260936092) * 10 ^ 70 +
        8419566945678540244598807703189030324825483586038641692241517845798800) : ℚ) := by
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

theorem recurrence5C0_coeff_64 :
    remainder7Coefficient0.coeff 64 =
      -(((719686177566377803399882653297752870310 * 10 ^ 70 +
        3149356717942084099915577717538477345159368241147758174047884482347060) * 10 ^ 70 +
        5310595348812716456205182724803412582123820056782100236165425040280600) : ℚ) := by
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

theorem recurrence5C0_coeff_65 :
    remainder7Coefficient0.coeff 65 =
      (((280889371719455291818599939720386480989 * 10 ^ 70 +
        7938802563144923576720185462936925364686691076003275748490428344133702) * 10 ^ 70 +
        0218562566299795328130960874811190270006568356919391082185295837714500) : ℚ) := by
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

theorem recurrence5C0_coeff_66 :
    remainder7Coefficient0.coeff 66 =
      -(((86838390668895088481903497456792890604 * 10 ^ 70 +
        0345960081250455125125307694777648996750016089634837675310878661116614) * 10 ^ 70 +
        5708923395088774563128637896451309893515716096343673989658030337195600) : ℚ) := by
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

theorem recurrence5C0_coeff_67 :
    remainder7Coefficient0.coeff 67 =
      (((16306246705588576411208798896532487486 * 10 ^ 70 +
        3215691994213056015068009760750960081868098311170762509791881719047457) * 10 ^ 70 +
        9701816572886996672346057482757892151280053517864041091028149138100400) : ℚ) := by
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

theorem recurrence5C0_coeff_68 :
    remainder7Coefficient0.coeff 68 =
      (((2168295487138244923417913298235211224 * 10 ^ 70 +
        4044092626158367473480577941528595086487542709398752582305578492794740) * 10 ^ 70 +
        2839871603316831583856938903402831845161092256395924445130145772892200) : ℚ) := by
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

theorem recurrence5C0_coeff_69 :
    remainder7Coefficient0.coeff 69 =
      -(((3664179009963021418686699948231695811 * 10 ^ 70 +
        2643767207022873742928113129351322626654604772315437073821454115015497) * 10 ^ 70 +
        0296215473098415897015666692586534788656524215597962336287145161673500) : ℚ) := by
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

theorem recurrence5C0_coeff_70 :
    remainder7Coefficient0.coeff 70 =
      (((1911172683317283413602587072080793761 * 10 ^ 70 +
        6162202573476189713858834876361711044224397788519754491163998141402545) * 10 ^ 70 +
        3774936573057029560740013032248101128939096132230990309411609408084100) : ℚ) := by
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

theorem recurrence5C0_coeff_71 :
    remainder7Coefficient0.coeff 71 =
      -(((649089845708781725918220795025204273 * 10 ^ 70 +
        1669239846801338793408944864034557762687741933683806854116955963988903) * 10 ^ 70 +
        0720197901743685674578528603668955701090875626384862093485669898433600) : ℚ) := by
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

theorem recurrence5C0_coeff_72 :
    remainder7Coefficient0.coeff 72 =
      (((147776373074621610818035990130057117 * 10 ^ 70 +
        8772869893925500433278319730371973726953441445759260568804020231834001) * 10 ^ 70 +
        3848588808276495134138237128688530195301903840787541927825589803622800) : ℚ) := by
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

theorem recurrence5C0_coeff_73 :
    remainder7Coefficient0.coeff 73 =
      -(((17552901927930098500221291737503152 * 10 ^ 70 +
        4733997638205847404768086305268314025994338663622094437587088144789859) * 10 ^ 70 +
        9138705578495017132035592111077609980923415294245132791933244355735500) : ℚ) := by
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

theorem recurrence5C0_coeff_74 :
    remainder7Coefficient0.coeff 74 =
      -(((1408938487289987084416991636620179 * 10 ^ 70 +
        6959035552335976021258639709518396010900926670407682392686205967931394) * 10 ^ 70 +
        6827515643993902802929748424321294310005470107484272642551102672107200) : ℚ) := by
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

theorem recurrence5C0_coeff_75 :
    remainder7Coefficient0.coeff 75 =
      (((1003027400475099197649105315510029 * 10 ^ 70 +
        1308941196709880316035146088816529003184748836210081599636958214880567) * 10 ^ 70 +
        3740288705294235555554605534352319607294460953502528525384404117634900) : ℚ) := by
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

theorem recurrence5C0_coeff_76 :
    remainder7Coefficient0.coeff 76 =
      -(((152922664346163787977457807376287 * 10 ^ 70 +
        2764033281982808879130836776910707568431484106465010144965508063628116) * 10 ^ 70 +
        4532833407205725388643524831797314215515044086309275752231560892829200) : ℚ) := by
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

theorem recurrence5C0_coeff_77 :
    remainder7Coefficient0.coeff 77 =
      -(((1141237593406432259428694812810 * 10 ^ 70 +
        1597452924110703353320181611787637242983179087769304666966861021355699) * 10 ^ 70 +
        3143816179006249520189917827438767605709711756890755731720160100676400) : ℚ) := by
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

theorem recurrence5C0_coeff_78 :
    remainder7Coefficient0.coeff 78 =
      (((1890694466184193372708948421663 * 10 ^ 70 +
        3265177583364361244612532968098083686711347708081215324031066965070246) * 10 ^ 70 +
        2845888629507477920107925229095817833066353337517732865587425407397800) : ℚ) := by
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

theorem recurrence5C0_coeff_79 :
    remainder7Coefficient0.coeff 79 =
      (((458050984484617742450235318171 * 10 ^ 70 +
        8535292860428834385931611938795127562511230566491951753476043921843758) * 10 ^ 70 +
        8695732965434993037833657206859726533590965158153208027541947473153300) : ℚ) := by
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

theorem recurrence5C0_coeff_80 :
    remainder7Coefficient0.coeff 80 =
      -(((157845728812479329550429125969 * 10 ^ 70 +
        8322968285837173055598475502131480448389326403457823323563646460376776) * 10 ^ 70 +
        3643835090316473249586776019411593483125913346876053394913682520225200) : ℚ) := by
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

theorem recurrence5C0_coeff_81 :
    remainder7Coefficient0.coeff 81 =
      (((7073511337725100179962869969 * 10 ^ 70 +
        3247056352002797664943806053225564930831703890971590246550540660912522) * 10 ^ 70 +
        7235917539423429345614127146107231506906906152573563682200594042309100) : ℚ) := by
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

theorem recurrence5C0_coeff_82 :
    remainder7Coefficient0.coeff 82 =
      (((1144729829415442013739630619 * 10 ^ 70 +
        7399484369445518132158204012530554070653916363199420341340580951693627) * 10 ^ 70 +
        4961984703876526085102136603319404267792454600482438065997691975687900) : ℚ) := by
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

theorem recurrence5C0_coeff_83 :
    remainder7Coefficient0.coeff 83 =
      -(((20030881010336799704514853 * 10 ^ 70 +
        7908662109328630650854611578575069671025878821522459985317012253171057) * 10 ^ 70 +
        3076743694872341668373877531003795741639344995679810078928047085959700) : ℚ) := by
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

theorem recurrence5C0_coeff_84 :
    remainder7Coefficient0.coeff 84 =
      -(((46124915926125853507119 * 10 ^ 70 +
        3087570402812029906407284303664036779779700940772685386039116076008438) * 10 ^ 70 +
        2714151177703274012456096570984688992356232848917866324540513853405400) : ℚ) := by
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

theorem recurrence5C0_coeff_85 :
    remainder7Coefficient0.coeff 85 =
      (((238193801912679644342 * 10 ^ 70 +
        9153428417952291744740482273313182492430055369360657216089240525618643) * 10 ^ 70 +
        9973650838350753771863311732418152847918447104971966339951464493570900) : ℚ) := by
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

theorem recurrence5C0_coeff_86 :
    remainder7Coefficient0.coeff 86 =
      -(((171559361212805156 * 10 ^ 70 +
        7704550613142743225714329810818397985723916716118494364937279152596181) * 10 ^ 70 +
        5221777699471252854218841329784006696570200672767771521984204686578000) : ℚ) := by
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

theorem recurrence5C0_coeff_87 :
    remainder7Coefficient0.coeff 87 =
      (((5209116126870 * 10 ^ 70 +
        4885071110470606579691760175672717076399907211131260617880672954003718) * 10 ^ 70 +
        5420790376879655959915435709609219266167472673780784225470842870679000) : ℚ) := by
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

theorem recurrence5C0_coeff_88 :
    remainder7Coefficient0.coeff 88 =
      -(((927037 * 10 ^ 70 +
        4104281385090204337589455937976768067173631172597890319603141623827532) * 10 ^ 70 +
        2427124817368784950967216852004366970391858104331311383428698675793700) : ℚ) := by
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
