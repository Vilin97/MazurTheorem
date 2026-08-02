/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData5
import Mathlib.Tactic.NormNum

/-!
# Recurrence 5 lookup certificate: B1 source coefficients, low half

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence5B1_coeff_0 :
    remainder6Coefficient1.coeff 0 =
      (0 : ℚ) := by
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

theorem recurrence5B1_coeff_1 :
    remainder6Coefficient1.coeff 1 =
      (-1233333102038599767025177989052174038378110465183077784 : ℚ) := by
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

theorem recurrence5B1_coeff_2 :
    remainder6Coefficient1.coeff 2 =
      (6744795161052376527847480813541934195323107839531288649742 : ℚ) := by
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

theorem recurrence5B1_coeff_3 :
    remainder6Coefficient1.coeff 3 =
      (-17144545448446729231271888388059049635765137714334105630005476 : ℚ) := by
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

theorem recurrence5B1_coeff_4 :
    remainder6Coefficient1.coeff 4 =
      (21665105922510052547683128461157255762150652249151751584433670082 : ℚ) := by
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

theorem recurrence5B1_coeff_5 :
    remainder6Coefficient1.coeff 5 =
      (-13598299462801716925139003155686688002700325639797923034409490767794 : ℚ) := by
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

theorem recurrence5B1_coeff_6 :
    remainder6Coefficient1.coeff 6 =
      (2495818431381336910434728763862007606140075504143986383890946992684898 : ℚ) := by
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

theorem recurrence5B1_coeff_7 :
    remainder6Coefficient1.coeff 7 =
      ((214 * 10 ^ 70 +
        8763094795863408157459753091528764884468795699957281460273405156300743) : ℚ) := by
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

theorem recurrence5B1_coeff_8 :
    remainder6Coefficient1.coeff 8 =
      -((188002 * 10 ^ 70 +
        1338696222779092985715891648945316468251617607688079632142610404556036) : ℚ) := by
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

theorem recurrence5B1_coeff_9 :
    remainder6Coefficient1.coeff 9 =
      ((77613412 * 10 ^ 70 +
        2046789170569417694225479650299481610798206716254043570939088757592568) : ℚ) := by
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

theorem recurrence5B1_coeff_10 :
    remainder6Coefficient1.coeff 10 =
      -((21191317762 * 10 ^ 70 +
        1910496439400543927732784129911087867477392531935184302225539703725890) : ℚ) := by
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

theorem recurrence5B1_coeff_11 :
    remainder6Coefficient1.coeff 11 =
      ((4222856260731 * 10 ^ 70 +
        2592515069920841339873902448191479187000729760389708698015909564061728) : ℚ) := by
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

theorem recurrence5B1_coeff_12 :
    remainder6Coefficient1.coeff 12 =
      -((644719168616171 * 10 ^ 70 +
        6029170106872123200965013377413888311106435508323153585972713142036660) : ℚ) := by
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

theorem recurrence5B1_coeff_13 :
    remainder6Coefficient1.coeff 13 =
      ((77740987899521133 * 10 ^ 70 +
        7664768157963552539462686683878731038760722007911001818563971356179332) : ℚ) := by
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

theorem recurrence5B1_coeff_14 :
    remainder6Coefficient1.coeff 14 =
      -((7566585991146283647 * 10 ^ 70 +
        5259406380494149283076746162989331840632969328668587715125391904926548) : ℚ) := by
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

theorem recurrence5B1_coeff_15 :
    remainder6Coefficient1.coeff 15 =
      ((604577157241289623699 * 10 ^ 70 +
        6978286248433897251176965155260498037873381559681913025445547056594760) : ℚ) := by
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

theorem recurrence5B1_coeff_16 :
    remainder6Coefficient1.coeff 16 =
      -((40203955406512336803138 * 10 ^ 70 +
        0306776008439598172709873136307409480488115214873508637886108437249748) : ℚ) := by
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

theorem recurrence5B1_coeff_17 :
    remainder6Coefficient1.coeff 17 =
      ((2250892977652090596337722 * 10 ^ 70 +
        8816261814163947443550935780662528144181306621853241525151690938722585) : ℚ) := by
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

theorem recurrence5B1_coeff_18 :
    remainder6Coefficient1.coeff 18 =
      -((107152290350756026689935290 * 10 ^ 70 +
        7373072928632060359027554839074699374385674331187498664865316253950185) : ℚ) := by
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

theorem recurrence5B1_coeff_19 :
    remainder6Coefficient1.coeff 19 =
      ((4374726901205978437111835858 * 10 ^ 70 +
        0974517323618007879701423287022746782872511933697294144207812567946086) : ℚ) := by
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

theorem recurrence5B1_coeff_20 :
    remainder6Coefficient1.coeff 20 =
      -((154351242780941649618203564436 * 10 ^ 70 +
        6577601922213417647884403936025757354199908346858535119958299660523184) : ℚ) := by
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

theorem recurrence5B1_coeff_21 :
    remainder6Coefficient1.coeff 21 =
      ((4738414423938904353570723033911 * 10 ^ 70 +
        8840028082255829733664764917730899881948306502538279032692590679309160) : ℚ) := by
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

theorem recurrence5B1_coeff_22 :
    remainder6Coefficient1.coeff 22 =
      -((127345341086984421183784128315642 * 10 ^ 70 +
        0806566608881613151358362728367788036266126878159628141428300185454211) : ℚ) := by
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

theorem recurrence5B1_coeff_23 :
    remainder6Coefficient1.coeff 23 =
      ((3012872394605316268379558063545555 * 10 ^ 70 +
        7610375095942236763292015224942808560785697550302793216875801748775772) : ℚ) := by
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

theorem recurrence5B1_coeff_24 :
    remainder6Coefficient1.coeff 24 =
      -((63072675251515285696391101324657321 * 10 ^ 70 +
        0698344022870220611224330447853115965462767108823576657597720888256347) : ℚ) := by
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

theorem recurrence5B1_coeff_25 :
    remainder6Coefficient1.coeff 25 =
      ((1173827105241917635315086897589102881 * 10 ^ 70 +
        4228378112383015768201433000397549006743438757109198866730038515150828) : ℚ) := by
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

theorem recurrence5B1_coeff_26 :
    remainder6Coefficient1.coeff 26 =
      -((19505498996772522752435792944615351499 * 10 ^ 70 +
        2370567346754873944228164070941010670574092120175071136165416013553081) : ℚ) := by
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

theorem recurrence5B1_coeff_27 :
    remainder6Coefficient1.coeff 27 =
      ((290572871215801936192991594765457542440 * 10 ^ 70 +
        6003832070639479558969794200367648514010842187113037160388298898689919) : ℚ) := by
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

theorem recurrence5B1_coeff_28 :
    remainder6Coefficient1.coeff 28 =
      -((3895256318877755560988159931244863048056 * 10 ^ 70 +
        5324950604505556527003210185455603283419351968993191386440548449563792) : ℚ) := by
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

theorem recurrence5B1_coeff_29 :
    remainder6Coefficient1.coeff 29 =
      ((47155620626329922433504102554537552184204 * 10 ^ 70 +
        5188577212803856978657626189000550998137750046000006656079980854957034) : ℚ) := by
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

theorem recurrence5B1_coeff_30 :
    remainder6Coefficient1.coeff 30 =
      -((517233639665122519569095573163216846354928 * 10 ^ 70 +
        4882820664840591175214941319435311044004337483909544896059950141642078) : ℚ) := by
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

theorem recurrence5B1_coeff_31 :
    remainder6Coefficient1.coeff 31 =
      ((5156438973872480861060558128288315225876095 * 10 ^ 70 +
        2783392902731863096261584561644517184982047688877554578004550957240548) : ℚ) := by
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

theorem recurrence5B1_coeff_32 :
    remainder6Coefficient1.coeff 32 =
      -((46859583538529654466873753398259952496612950 * 10 ^ 70 +
        8701976508251439575835010848569957468886713102497405848274738878855982) : ℚ) := by
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

theorem recurrence5B1_coeff_33 :
    remainder6Coefficient1.coeff 33 =
      ((389256276436585652255756139176676451137880123 * 10 ^ 70 +
        6131513946918112844390153610581753945601669214401023814053940259478466) : ℚ) := by
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

theorem recurrence5B1_coeff_34 :
    remainder6Coefficient1.coeff 34 =
      -((2963448776080579123734251050134249846154523169 * 10 ^ 70 +
        7872753808136984699900210238060132197024696697455186877728639974775178) : ℚ) := by
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

theorem recurrence5B1_coeff_35 :
    remainder6Coefficient1.coeff 35 =
      ((20727973236416584947327816539323839814041120401 * 10 ^ 70 +
        4228259193157228973725208837359385727685279688727229231729307296606870) : ℚ) := by
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

theorem recurrence5B1_coeff_36 :
    remainder6Coefficient1.coeff 36 =
      -((133514286562547481281990628535664398144076813808 * 10 ^ 70 +
        8760769938682554992633147522731160834913618831973847660419946767067404) : ℚ) := by
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

theorem recurrence5B1_coeff_37 :
    remainder6Coefficient1.coeff 37 =
      ((793721604308880451476552585007337051809844367468 * 10 ^ 70 +
        0997398437660804870068796486741716932499446740582470981364659221130319) : ℚ) := by
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

theorem recurrence5B1_coeff_38 :
    remainder6Coefficient1.coeff 38 =
      -((4363987479421407793071774947004226587329195615973 * 10 ^ 70 +
        3293339585758327277151470528523801517312459480586604975736235973870024) : ℚ) := by
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

theorem recurrence5B1_coeff_39 :
    remainder6Coefficient1.coeff 39 =
      ((22234573143311079171560866518776617364712561917296 * 10 ^ 70 +
        6421748979134489241602689973700501419861362759984913000351268845228674) : ℚ) := by
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

theorem recurrence5B1_coeff_40 :
    remainder6Coefficient1.coeff 40 =
      -((105174792694178911114768136936433068005418717423915 * 10 ^ 70 +
        8098874519685745618565099900122769393512008606990797434894233070273993) : ℚ) := by
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

theorem recurrence5B1_coeff_41 :
    remainder6Coefficient1.coeff 41 =
      ((462694518167863835914172242128161201623458506665162 * 10 ^ 70 +
        5756452325158517016697990675908425896699523802824219383583143859033854) : ℚ) := by
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

theorem recurrence5B1_coeff_42 :
    remainder6Coefficient1.coeff 42 =
      -((1896251617421626869101843318852080018853261107529902 * 10 ^ 70 +
        5974084732411254407981944598239630421600002992225564417692043918211687) : ℚ) := by
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

theorem recurrence5B1_coeff_43 :
    remainder6Coefficient1.coeff 43 =
      ((7250942657251063766885303797208568711921077369907979 * 10 ^ 70 +
        2738472067753035269614527437104449346609266394427167668138641320608414) : ℚ) := by
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

theorem recurrence5B1_coeff_44 :
    remainder6Coefficient1.coeff 44 =
      -((25907687424515510906686670450350770399628233136168169 * 10 ^ 70 +
        4890269662209917496805378665299480726642874669605063012806648385029168) : ℚ) := by
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

theorem recurrence5B1_coeff_45 :
    remainder6Coefficient1.coeff 45 =
      ((86616354642318466026770224983370710971831949429451144 * 10 ^ 70 +
        2871521604685802507123501594222398391290312560915892437939797261787639) : ℚ) := by
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

theorem recurrence5B1_coeff_46 :
    remainder6Coefficient1.coeff 46 =
      -((271315124539341601391603099952335553839982359618649579 * 10 ^ 70 +
        0459266026265512871836960111605788578029668104834895462958592241572978) : ℚ) := by
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

theorem recurrence5B1_coeff_47 :
    remainder6Coefficient1.coeff 47 =
      ((797228399002966810420627974548691399917561366841966960 * 10 ^ 70 +
        9962411634916940135049693189730569107276637643651956188991506213686362) : ℚ) := by
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

theorem recurrence5B1_coeff_48 :
    remainder6Coefficient1.coeff 48 =
      -((2200014739886310563532405547410180336016784009920733897 * 10 ^ 70 +
        1387190855823977046125809083808926767753676974665130563093439703467401) : ℚ) := by
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

theorem recurrence5B1_coeff_49 :
    remainder6Coefficient1.coeff 49 =
      ((5707830036992132231858061358226568675073812205335455159 * 10 ^ 70 +
        9340214463791831515289021327617936985208886120752358949358754673868527) : ℚ) := by
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

theorem recurrence5B1_coeff_50 :
    remainder6Coefficient1.coeff 50 =
      -((13936642994443850985644275973295354979125560308618907280 * 10 ^ 70 +
        8508249173298391681059257906276701894192966895592215910856473640222888) : ℚ) := by
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

theorem recurrence5B1_coeff_51 :
    remainder6Coefficient1.coeff 51 =
      ((32055164365341675595532387086250130145053534130099163476 * 10 ^ 70 +
        5939552789680916889958805204648072117280242498383052317614052750973547) : ℚ) := by
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

theorem recurrence5B1_coeff_52 :
    remainder6Coefficient1.coeff 52 =
      -((69514386900494112301977979571447203377132214134577632536 * 10 ^ 70 +
        1169892844223251069429478268037071348213381201800426513244888087907250) : ℚ) := by
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

theorem recurrence5B1_coeff_53 :
    remainder6Coefficient1.coeff 53 =
      ((142248198951577399111703653987846892152314631070325692021 * 10 ^ 70 +
        4614438227580000980212497524529935090715795931206162984262371766443455) : ℚ) := by
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

theorem recurrence5B1_coeff_54 :
    remainder6Coefficient1.coeff 54 =
      -((274883242650361566122461317926323710773526795422848261806 * 10 ^ 70 +
        1091467306736611695039122258070373352650395515867508890188170870036841) : ℚ) := by
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

theorem recurrence5B1_coeff_55 :
    remainder6Coefficient1.coeff 55 =
      ((501983791979574224726251163414187764038119593992539072315 * 10 ^ 70 +
        1983971431823010187011894172874973816057010649058343337351824197764466) : ℚ) := by
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

theorem recurrence5B1_coeff_56 :
    remainder6Coefficient1.coeff 56 =
      -((866880140085221142623707956487449637430699977719884642632 * 10 ^ 70 +
        1008145006908709802334681883219946185914793309198799778034042515906067) : ℚ) := by
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

theorem recurrence5B1_coeff_57 :
    remainder6Coefficient1.coeff 57 =
      ((1416519777508094251205058511727648256522823276901855723693 * 10 ^ 70 +
        1991035848251700667439444564622815800336278286048206015544710260966485) : ℚ) := by
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

theorem recurrence5B1_coeff_58 :
    remainder6Coefficient1.coeff 58 =
      -((2191421103672412796215333195511950717670892655081153440625 * 10 ^ 70 +
        6105187042025519495730060286825001041181105374527663276639000482141819) : ℚ) := by
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

theorem recurrence5B1_coeff_59 :
    remainder6Coefficient1.coeff 59 =
      ((3211395285104589026695699273906152256870181101647710178836 * 10 ^ 70 +
        0613726962365986586154906259932529161682597800226079758392761866535878) : ℚ) := by
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

theorem recurrence5B1_coeff_60 :
    remainder6Coefficient1.coeff 60 =
      -((4459969054471307632197263488384575224013172986715803427318 * 10 ^ 70 +
        4510339174901192008547788072475806690212935159599475971944303821017443) : ℚ) := by
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

theorem recurrence5B1_coeff_61 :
    remainder6Coefficient1.coeff 61 =
      ((5872543702192394094762659952528744538406218388434060805628 * 10 ^ 70 +
        7671408932888570620687898493954086337057342861218518950321185679613797) : ℚ) := by
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

theorem recurrence5B1_coeff_62 :
    remainder6Coefficient1.coeff 62 =
      -((7334056441228241189103451172795491203409521040771486602425 * 10 ^ 70 +
        8101109070824340195824457041000119823421397708304988476574931313645945) : ℚ) := by
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

theorem recurrence5B1_coeff_63 :
    remainder6Coefficient1.coeff 63 =
      ((8690290405356740861131980466182683303058651703137073752506 * 10 ^ 70 +
        1569341471162575605415280666138758071262648409560633354527676957667926) : ℚ) := by
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

theorem recurrence5B1_coeff_64 :
    remainder6Coefficient1.coeff 64 =
      -((9772958063792362715469941408405734813507644123140646662799 * 10 ^ 70 +
        2381397226498399901842850593989267406842491116336837999505788616322939) : ℚ) := by
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

theorem recurrence5B1_coeff_65 :
    remainder6Coefficient1.coeff 65 =
      ((10433499126056046006605880476822856499890741224985705273452 * 10 ^ 70 +
        1103349813035892156583929232483211789024702732124265126130361240848240) : ℚ) := by
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

theorem recurrence5B1_coeff_66 :
    remainder6Coefficient1.coeff 66 =
      -((10576371886603603828027158272470065714420926172710647070662 * 10 ^ 70 +
        8408734486927429300992183575446402954435756536125346709745594510997678) : ℚ) := by
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

theorem recurrence5B1_coeff_67 :
    remainder6Coefficient1.coeff 67 =
      ((10181585048761854440807157637358365569308241962999868075907 * 10 ^ 70 +
        6911916864481940868784584075036591813697306858309123962039117439415454) : ℚ) := by
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

theorem recurrence5B1_coeff_68 :
    remainder6Coefficient1.coeff 68 =
      -((9309172208899692294692475169459158689332245664537867465748 * 10 ^ 70 +
        2387623811623260903210472178406283576315403151660796533431510443360424) : ℚ) := by
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

theorem recurrence5B1_coeff_69 :
    remainder6Coefficient1.coeff 69 =
      ((8084248634494591448085243951429559995305638001919973557822 * 10 ^ 70 +
        3697664372869693769827453176474776364030091989115496334522258695666360) : ℚ) := by
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

theorem recurrence5B1_coeff_70 :
    remainder6Coefficient1.coeff 70 =
      -((6667743273352928881992005736700594880890502881293365009081 * 10 ^ 70 +
        5668999416980582697884491162324931627635130608374234126371309022192419) : ℚ) := by
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

theorem recurrence5B1_coeff_71 :
    remainder6Coefficient1.coeff 71 =
      ((5222170785787693475952132522272987577122934093693609697924 * 10 ^ 70 +
        9589607111967252163179213150344187307083237843754254750332087057105566) : ℚ) := by
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

theorem recurrence5B1_coeff_72 :
    remainder6Coefficient1.coeff 72 =
      -((3882318653474277038035706004544186922944008292961572754525 * 10 ^ 70 +
        9068350800893508415045435815307304070718164832404155128719456006163002) : ℚ) := by
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

theorem recurrence5B1_coeff_73 :
    remainder6Coefficient1.coeff 73 =
      ((2737696065764670234913825797840439973033958494997638807985 * 10 ^ 70 +
        2613171134807025626278521371580455048675287025764255337841005794600279) : ℚ) := by
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

theorem recurrence5B1_coeff_74 :
    remainder6Coefficient1.coeff 74 =
      -((1828738741166819381084725105286531952302328128179289867609 * 10 ^ 70 +
        6424052933881058094424634281004758133663131890532365928514863135262806) : ℚ) := by
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
