/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData5
import Mathlib.Tactic.NormNum

/-!
# Recurrence 5 lookup certificate: B2 source coefficients, high half

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence5B2_coeff_73 :
    remainder6Coefficient2.coeff 73 =
      ((48599685231303791167540017796854655473235154298391511542 * 10 ^ 70 +
        9268613880701467853991832449274816765184100936812687962990841112832929) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_74 :
    remainder6Coefficient2.coeff 74 =
      -((27779899192589944260433799436627908900960488493145195239 * 10 ^ 70 +
        2978036119455528956287613452640247909313221393529923750860147507638142) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_75 :
    remainder6Coefficient2.coeff 75 =
      ((14501647251879882047632711538946272697795118590870713681 * 10 ^ 70 +
        2918453471085610019051783395722583727401116256159488857986352057513123) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_76 :
    remainder6Coefficient2.coeff 76 =
      -((6598423335347949964850616633574166380428319366689856277 * 10 ^ 70 +
        3114443383246950260768040944860024392334188938296101576450139001630304) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_77 :
    remainder6Coefficient2.coeff 77 =
      ((2258160633962738043300824629310413237565049823573053469 * 10 ^ 70 +
        6572327378119491599708118460501410314343498463097848778840617446273273) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_78 :
    remainder6Coefficient2.coeff 78 =
      -((126963224508497319105497374584311056955610448551655894 * 10 ^ 70 +
        8358322811211107927324656608519616408820745635531835018070184408446371) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_79 :
    remainder6Coefficient2.coeff 79 =
      -((724413569614228005180383910664249496744714528335919267 * 10 ^ 70 +
        1732392049784942503973609810888951059539778594336372231888684302828172) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_80 :
    remainder6Coefficient2.coeff 80 =
      ((893928773649319670528703956201318547898222374743285784 * 10 ^ 70 +
        9182756035758564605028869618395670290830339745095152783755124072643381) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_81 :
    remainder6Coefficient2.coeff 81 =
      -((747351569006862732713820188377894956085529807845407151 * 10 ^ 70 +
        5263264289829282098981778859562522630183334970528907357582557286536323) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_82 :
    remainder6Coefficient2.coeff 82 =
      ((497271259000702622388794449320603971270119138809454993 * 10 ^ 70 +
        2337408219657196281306875636377553562365438390806971843075216462224687) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_83 :
    remainder6Coefficient2.coeff 83 =
      -((257407616071965195857673443260308658804418260856870478 * 10 ^ 70 +
        0999377228158741505684566614370588212365332929580723587819838565569943) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_84 :
    remainder6Coefficient2.coeff 84 =
      ((78012477472994335588428125781213192459523710299517298 * 10 ^ 70 +
        2823899096258171634170892997356757715368988699976636900471950633543049) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_85 :
    remainder6Coefficient2.coeff 85 =
      ((30100592275839493383869274937121834641113531359376650 * 10 ^ 70 +
        1205459981700993865846555185038705016192136701677611059991227145133528) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_86 :
    remainder6Coefficient2.coeff 86 =
      -((77916939059522364995031465366870469905521492961412174 * 10 ^ 70 +
        7330563526133869058804911174614151202054512968426253512544934467688369) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_87 :
    remainder6Coefficient2.coeff 87 =
      ((85071625373549289793522191741632327329665252071455571 * 10 ^ 70 +
        3410850747470432015009945465643378400717185719685379702916957274088885) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_88 :
    remainder6Coefficient2.coeff 88 =
      -((70977265933666374140972546731764105791791274868303143 * 10 ^ 70 +
        7479270296972439088289354383515952585812966298682020777429369196079657) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_89 :
    remainder6Coefficient2.coeff 89 =
      ((50150763195321775791031760474792187922558712487997694 * 10 ^ 70 +
        3236193234216076645069510150942951467100539363711198121049238949334752) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_90 :
    remainder6Coefficient2.coeff 90 =
      -((31025126271699610155562539388782630138636994439737611 * 10 ^ 70 +
        8993968811764216243406136169217122142633848396370306612387525190292024) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_91 :
    remainder6Coefficient2.coeff 91 =
      ((16970499385440208377440044227789670041791189691602260 * 10 ^ 70 +
        9150805926500339185971461656177213120589050117693984677819560340491943) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_92 :
    remainder6Coefficient2.coeff 92 =
      -((8175020980016097633200263425903525053288785000927248 * 10 ^ 70 +
        9399412649615291009141984515300485409222518991278414149698632593432644) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_93 :
    remainder6Coefficient2.coeff 93 =
      ((3401809131624074734193211388302023112004005044357671 * 10 ^ 70 +
        2389158183743668649573776034338656226477184485078475557446638123793183) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_94 :
    remainder6Coefficient2.coeff 94 =
      -((1163185866511983675534984731474977831080573941160263 * 10 ^ 70 +
        2338450735561994791351502766735049584020016702532954335537756350374596) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_95 :
    remainder6Coefficient2.coeff 95 =
      ((279610221925612080799859556846211044304465944753243 * 10 ^ 70 +
        2056742145966042586938253520152812672236799664608304728034836063135602) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_96 :
    remainder6Coefficient2.coeff 96 =
      -((8428496946274601814182668825659645514868427186552 * 10 ^ 70 +
        4295271073379253508249597985643952771431177125059578764292843606049552) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_97 :
    remainder6Coefficient2.coeff 97 =
      -((37738868628617613850723855000495903869917909625830 * 10 ^ 70 +
        0852595593779336877956388753698454713916439485786439593431155173629719) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_98 :
    remainder6Coefficient2.coeff 98 =
      ((25279272741708456595421114756012733385317749031885 * 10 ^ 70 +
        5493615368495639035871378045746365029251162330126000071403202457113178) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_99 :
    remainder6Coefficient2.coeff 99 =
      -((9522193911659574346474741099383635731794673660151 * 10 ^ 70 +
        3160020556912508847523869109553062272999215184941358327137342834894006) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_100 :
    remainder6Coefficient2.coeff 100 =
      ((1308343023165769797495116798222559592503158133531 * 10 ^ 70 +
        7635865144354870884468239244552940962441385264589803309596463434265048) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_101 :
    remainder6Coefficient2.coeff 101 =
      ((1294409822160764814007189902723806326569743864688 * 10 ^ 70 +
        6885490523069061337500835278122918558074509039279346184233465603252530) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_102 :
    remainder6Coefficient2.coeff 102 =
      -((1457532236183134232561037564161098688736909008316 * 10 ^ 70 +
        8332757735392108399542816640873668585183673958188887325772081046391499) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_103 :
    remainder6Coefficient2.coeff 103 =
      ((988362580170186405251125559736707020970829784175 * 10 ^ 70 +
        7942292588601449832128916290213202711750373651818584188011050419311992) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_104 :
    remainder6Coefficient2.coeff 104 =
      -((551861124749112306058478137876384445924407669411 * 10 ^ 70 +
        0179791053225581208663370006851966912269755419139826330366913027954452) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_105 :
    remainder6Coefficient2.coeff 105 =
      ((277534389214183853394134689759151047894915301681 * 10 ^ 70 +
        0003537962945726711260898430901063968152076412170284904069807708652650) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_106 :
    remainder6Coefficient2.coeff 106 =
      -((130857083815360251488380598276968256217575939380 * 10 ^ 70 +
        7781338982346163278205785688954714462411888037977053689643044829371261) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_107 :
    remainder6Coefficient2.coeff 107 =
      ((58867891722179735247266920402075037546171214846 * 10 ^ 70 +
        8674689591595608319024527138031543150545262423399425580198374520308523) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_108 :
    remainder6Coefficient2.coeff 108 =
      -((25366747863442388336418006750612291774823405564 * 10 ^ 70 +
        4917020638140856778199452678742626045279602598894548203021183026587271) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_109 :
    remainder6Coefficient2.coeff 109 =
      ((10434853469348455139497887010914111613791698027 * 10 ^ 70 +
        0288863905889538598536150880150856052858458366643281068113652649611046) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_110 :
    remainder6Coefficient2.coeff 110 =
      -((4074065459812993088355855359391476934407685933 * 10 ^ 70 +
        3851010848658884161214376780599722948614593770895805180130388096279674) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_111 :
    remainder6Coefficient2.coeff 111 =
      ((1501582529385831839735530510272945785887455725 * 10 ^ 70 +
        7958647132243733180648404790241976723469380608381972171539497975003476) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_112 :
    remainder6Coefficient2.coeff 112 =
      -((520308991924203198927315534592870395609836476 * 10 ^ 70 +
        7921597093507513582828848252840676374402012778755696229611967827571037) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_113 :
    remainder6Coefficient2.coeff 113 =
      ((168973746115604636457906790392672827468280558 * 10 ^ 70 +
        6657257245800746522654299969779992699738882022885790676024507032428987) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_114 :
    remainder6Coefficient2.coeff 114 =
      -((51295175616213033871609773975107858976615518 * 10 ^ 70 +
        0914677220420011443245008815867549438214188852598827284101714563387729) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_115 :
    remainder6Coefficient2.coeff 115 =
      ((14520008116942477970197763919089124472029437 * 10 ^ 70 +
        2766822601505968961009330359311772311568978097312249228656335110328450) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_116 :
    remainder6Coefficient2.coeff 116 =
      -((3826405584733007218557593633924515914367677 * 10 ^ 70 +
        6056772151682717437932753363456262427380353849635304040413025160719319) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_117 :
    remainder6Coefficient2.coeff 117 =
      ((940594305767974602133541895195873658565811 * 10 ^ 70 +
        5504076539889095985616771418434543472496438698261949034362544708431560) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_118 :
    remainder6Coefficient2.coeff 118 =
      -((218284140881524580921752726806175781618415 * 10 ^ 70 +
        3236866983341947289623772879154473331476550547013296990455109241429906) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_119 :
    remainder6Coefficient2.coeff 119 =
      ((49330467729218528489700544406692904618891 * 10 ^ 70 +
        1827528484784908392734382156338559252069346977302752915210121027659102) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_120 :
    remainder6Coefficient2.coeff 120 =
      -((11345009349870368982385324382780380465581 * 10 ^ 70 +
        8251147506810811634222054525644769279471155349553374929285786928545667) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_121 :
    remainder6Coefficient2.coeff 121 =
      ((2667847642545719894925932709219888457567 * 10 ^ 70 +
        0466396785209572427762731178173143465024838113051997567632288474795720) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_122 :
    remainder6Coefficient2.coeff 122 =
      -((576083488551795460969639906020434002617 * 10 ^ 70 +
        9206699247658406749071494415663732629202462030222233829358287818707945) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_123 :
    remainder6Coefficient2.coeff 123 =
      ((82989663165578612519133865690186384789 * 10 ^ 70 +
        0259347909052464670307312886589665682232482935685176630742420842167938) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_124 :
    remainder6Coefficient2.coeff 124 =
      ((5508672996884803942182802505703761025 * 10 ^ 70 +
        0592064659961542675329131480412021859411117516444690469322170033032725) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_125 :
    remainder6Coefficient2.coeff 125 =
      -((8090790244339268206485123868987787368 * 10 ^ 70 +
        8487352718935295956240623090942694582707980720582369164589362225654248) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_126 :
    remainder6Coefficient2.coeff 126 =
      ((2646231571403608723732382026538525093 * 10 ^ 70 +
        9588530180433784736286182476044361892816144219302789758437842651515695) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_127 :
    remainder6Coefficient2.coeff 127 =
      -((433145954453278972916308394735242694 * 10 ^ 70 +
        4359560754449757024624084959399605244954985058626296397191504481536389) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_128 :
    remainder6Coefficient2.coeff 128 =
      ((5499155051187476475623468384174145 * 10 ^ 70 +
        1254477266854320924526548060020820988484083112488160569115753641618150) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_129 :
    remainder6Coefficient2.coeff 129 =
      ((14644442228487938748653730741022805 * 10 ^ 70 +
        0008953866221741351187004318210086273121544149677806444203452555899307) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_130 :
    remainder6Coefficient2.coeff 130 =
      -((3324608307471760695772340863824932 * 10 ^ 70 +
        2252766533771398151928465748226828800037319996136864810452534986708490) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_131 :
    remainder6Coefficient2.coeff 131 =
      ((280334742893617194673961770676587 * 10 ^ 70 +
        2446564632596472768720981531979414135188289215928506034190738979674121) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_132 :
    remainder6Coefficient2.coeff 132 =
      ((9068181044053674653722335555296 * 10 ^ 70 +
        1873633949010043981394764084138571871167439497171768848926838797983981) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_133 :
    remainder6Coefficient2.coeff 133 =
      -((3130475016044049810477927074372 * 10 ^ 70 +
        2379423632032145807015974551667715289253871970784281985357294982303969) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_134 :
    remainder6Coefficient2.coeff 134 =
      ((73622740150917879405787755606 * 10 ^ 70 +
        5168280459617905184842065024700457792989346885275200399652691396850351) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_135 :
    remainder6Coefficient2.coeff 135 =
      ((10045620265815068481274293739 * 10 ^ 70 +
        8280574427299620663867553280821784225831209675040538781296892725617634) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_136 :
    remainder6Coefficient2.coeff 136 =
      ((188383442518147293305095364 * 10 ^ 70 +
        2235185127942288597075139015171885480003591421915254058426192374993027) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_137 :
    remainder6Coefficient2.coeff 137 =
      ((1284234383367147490958064 * 10 ^ 70 +
        0756450501637377222403159914278633537109012469543620534536290176880272) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_138 :
    remainder6Coefficient2.coeff 138 =
      ((3184414845719719127819 * 10 ^ 70 +
        8241085134339655761307908030158948097556378745720782085669403465197870) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_139 :
    remainder6Coefficient2.coeff 139 =
      -((870654330344621713 * 10 ^ 70 +
        4705066291656197121458164050967722638498361577552255207966414526402482) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_140 :
    remainder6Coefficient2.coeff 140 =
      -((13291941571225729 * 10 ^ 70 +
        7694791863260470273460161742404202668832333179676349799598819356054578) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_141 :
    remainder6Coefficient2.coeff 141 =
      -((11551837670053 * 10 ^ 70 +
        7372888232063141806966649626184308182184762455316893231296073710725208) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_142 :
    remainder6Coefficient2.coeff 142 =
      -((1843302736 * 10 ^ 70 +
        2641183905269629220773977325092862024495701644198838862062737162826777) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_143 :
    remainder6Coefficient2.coeff 143 =
      -((41833 * 10 ^ 70 +
        6769415752606409216783188782830377669554171440031848370170515771772789) : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_144 :
    remainder6Coefficient2.coeff 144 =
      (-772747436405148042234850232988994618856223643876527211966243762975479 : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B2_coeff_145 :
    remainder6Coefficient2.coeff 145 =
      (-53701746906274322922389292413329009090012362832185396756764943 : ℚ) := by
  unfold
    remainder6Coefficient2
    remainder6Coefficient2Block1
    remainder6Coefficient2Block0
    remainder6Coefficient2Chunk18
    remainder6Coefficient2Chunk17
    remainder6Coefficient2Chunk16
    remainder6Coefficient2Chunk15
    remainder6Coefficient2Chunk14
    remainder6Coefficient2Chunk13
    remainder6Coefficient2Chunk12
    remainder6Coefficient2Chunk11
    remainder6Coefficient2Chunk10
    remainder6Coefficient2Chunk9
    remainder6Coefficient2Chunk8
    remainder6Coefficient2Chunk7
    remainder6Coefficient2Chunk6
    remainder6Coefficient2Chunk5
    remainder6Coefficient2Chunk4
    remainder6Coefficient2Chunk3
    remainder6Coefficient2Chunk2
    remainder6Coefficient2Chunk1
    remainder6Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
