/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData5
import Mathlib.Tactic.NormNum

/-!
# Recurrence 5 lookup certificate: B2 source coefficients, low half

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence5B2_coeff_0 :
    remainder6Coefficient2.coeff 0 =
      (10878351506404408088424943674109583579961283044613696 : ℚ) := by
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

theorem recurrence5B2_coeff_1 :
    remainder6Coefficient2.coeff 1 =
      (8575540471892424951206488410096511105878228940107034228 : ℚ) := by
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

theorem recurrence5B2_coeff_2 :
    remainder6Coefficient2.coeff 2 =
      (104679408795859278082331609546010429769197018550786987934060 : ℚ) := by
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

theorem recurrence5B2_coeff_3 :
    remainder6Coefficient2.coeff 3 =
      (-161964024850396557019751616976705286128780930691657032525541772 : ℚ) := by
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

theorem recurrence5B2_coeff_4 :
    remainder6Coefficient2.coeff 4 =
      (152234311257930507285143691757508433385256530460555201571197283092 : ℚ) := by
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

theorem recurrence5B2_coeff_5 :
    remainder6Coefficient2.coeff 5 =
      (-64605906396130641148063227302237344653584731396817949057963444656588 : ℚ) := by
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

theorem recurrence5B2_coeff_6 :
    remainder6Coefficient2.coeff 6 =
      (-3977819165814622223044303111487801946947324273452714956481266511841788 : ℚ) := by
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

theorem recurrence5B2_coeff_7 :
    remainder6Coefficient2.coeff 7 =
      ((1870 * 10 ^ 70 +
        2708313041368798656118274672741357179002795767503543443901624574392686) : ℚ) := by
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

theorem recurrence5B2_coeff_8 :
    remainder6Coefficient2.coeff 8 =
      -((1067285 * 10 ^ 70 +
        8802225454952958011195184097045658548755117146818487120249262207937278) : ℚ) := by
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

theorem recurrence5B2_coeff_9 :
    remainder6Coefficient2.coeff 9 =
      ((357126952 * 10 ^ 70 +
        5926949597517542172431891005196238996937356902597910406083984960035210) : ℚ) := by
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

theorem recurrence5B2_coeff_10 :
    remainder6Coefficient2.coeff 10 =
      -((83501812694 * 10 ^ 70 +
        7805813663707450362693122194832085081342896498022313692988813938027377) : ℚ) := by
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

theorem recurrence5B2_coeff_11 :
    remainder6Coefficient2.coeff 11 =
      ((14616282124497 * 10 ^ 70 +
        3790194883658403932530647683927684394133268570636731332947703574702830) : ℚ) := by
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

theorem recurrence5B2_coeff_12 :
    remainder6Coefficient2.coeff 12 =
      -((1990159899775983 * 10 ^ 70 +
        9476345317299075215656109637950118713756894125739880378885065157584062) : ℚ) := by
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

theorem recurrence5B2_coeff_13 :
    remainder6Coefficient2.coeff 13 =
      ((216267390536546457 * 10 ^ 70 +
        5989198722257554311229343881534329305748289070840885654592413418978336) : ℚ) := by
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

theorem recurrence5B2_coeff_14 :
    remainder6Coefficient2.coeff 14 =
      -((19118816459534268712 * 10 ^ 70 +
        7701387021937905670314917033946661765049578114729023409768321023421508) : ℚ) := by
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

theorem recurrence5B2_coeff_15 :
    remainder6Coefficient2.coeff 15 =
      ((1396070781361377701629 * 10 ^ 70 +
        2484140662365357257162973395301533514685861818404208151292110820710980) : ℚ) := by
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

theorem recurrence5B2_coeff_16 :
    remainder6Coefficient2.coeff 16 =
      -((85268800949887450404951 * 10 ^ 70 +
        5864841267752010180378514502161797305184964947337081109060780413580258) : ℚ) := by
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

theorem recurrence5B2_coeff_17 :
    remainder6Coefficient2.coeff 17 =
      ((4402878421785205812429884 * 10 ^ 70 +
        2696024149721061531120565129471767131590627540760020037156496479051009) : ℚ) := by
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

theorem recurrence5B2_coeff_18 :
    remainder6Coefficient2.coeff 18 =
      -((193974138906564207975580091 * 10 ^ 70 +
        7512709950776024256178072524918098638880757842298961056435139961326406) : ℚ) := by
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

theorem recurrence5B2_coeff_19 :
    remainder6Coefficient2.coeff 19 =
      ((7350463732292667682801746605 * 10 ^ 70 +
        5699702895908500688861206367438517121563489323558222576364031637203866) : ℚ) := by
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

theorem recurrence5B2_coeff_20 :
    remainder6Coefficient2.coeff 20 =
      -((241299738756843104246814323869 * 10 ^ 70 +
        0468563377963921263909025497589432773896043552851898418177795937694784) : ℚ) := by
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

theorem recurrence5B2_coeff_21 :
    remainder6Coefficient2.coeff 21 =
      ((6906441389579017960752949643646 * 10 ^ 70 +
        5240555101732808731362467301676052600079722204577509902371099516757762) : ℚ) := by
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

theorem recurrence5B2_coeff_22 :
    remainder6Coefficient2.coeff 22 =
      -((173349744246040970179540065538516 * 10 ^ 70 +
        6577481096290538067074485672781207038436326957760736675277633085324610) : ℚ) := by
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

theorem recurrence5B2_coeff_23 :
    remainder6Coefficient2.coeff 23 =
      ((3835785093225042579692882730332666 * 10 ^ 70 +
        2892403559141140955671732967306785361381837643303804620283109071917827) : ℚ) := by
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

theorem recurrence5B2_coeff_24 :
    remainder6Coefficient2.coeff 24 =
      -((75187727787876069098087130256488001 * 10 ^ 70 +
        2891781840743723879210377541532804505807033120212432464467290363899408) : ℚ) := by
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

theorem recurrence5B2_coeff_25 :
    remainder6Coefficient2.coeff 25 =
      ((1311403891458939085379106776005262179 * 10 ^ 70 +
        6340809680441341301998185868622819687787094165890816085730877573929104) : ℚ) := by
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

theorem recurrence5B2_coeff_26 :
    remainder6Coefficient2.coeff 26 =
      -((20436924339000387195683065298650811476 * 10 ^ 70 +
        4810909968013210370410502914086410662038157087910080400130345322186282) : ℚ) := by
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

theorem recurrence5B2_coeff_27 :
    remainder6Coefficient2.coeff 27 =
      ((285661808449780648287950187041379081283 * 10 ^ 70 +
        1589860993781412022811472419198438408624287427885394490976566886196533) : ℚ) := by
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

theorem recurrence5B2_coeff_28 :
    remainder6Coefficient2.coeff 28 =
      -((3594215550139694952274227275183728889157 * 10 ^ 70 +
        7300130801044558224742932143589000026583455167692656136372610356821362) : ℚ) := by
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

theorem recurrence5B2_coeff_29 :
    remainder6Coefficient2.coeff 29 =
      ((40844220587125777538843037817742825788412 * 10 ^ 70 +
        2507194317530955722692424855388939722337936784359128657180681684039362) : ℚ) := by
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

theorem recurrence5B2_coeff_30 :
    remainder6Coefficient2.coeff 30 =
      -((420535090558665637160985202780792574623262 * 10 ^ 70 +
        5119254961621129320322733547654836033926605630638171652497746263207207) : ℚ) := by
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

theorem recurrence5B2_coeff_31 :
    remainder6Coefficient2.coeff 31 =
      ((3934676235944315023142562171149212790301657 * 10 ^ 70 +
        6344301456049031196841295539134363817474767175645657262458067597000960) : ℚ) := by
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

theorem recurrence5B2_coeff_32 :
    remainder6Coefficient2.coeff 32 =
      -((33548037061803570975765369579474110795266300 * 10 ^ 70 +
        9564691007389940937272940670230198353563816635406814014335772928373333) : ℚ) := by
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

theorem recurrence5B2_coeff_33 :
    remainder6Coefficient2.coeff 33 =
      ((261351341496980261170447137563177431861941169 * 10 ^ 70 +
        2047643242339127982795458313484363807262101887599781878801392268015644) : ℚ) := by
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

theorem recurrence5B2_coeff_34 :
    remainder6Coefficient2.coeff 34 =
      -((1864948499119472799047135982907850953273944538 * 10 ^ 70 +
        0723291537983818190080652521736510114315086183984160323284386395380246) : ℚ) := by
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

theorem recurrence5B2_coeff_35 :
    remainder6Coefficient2.coeff 35 =
      ((12218543839652029196179997127747930407367715643 * 10 ^ 70 +
        2547419680916694901172083780609595820332108432233492668082785366620228) : ℚ) := by
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

theorem recurrence5B2_coeff_36 :
    remainder6Coefficient2.coeff 36 =
      -((73663652515503631061675599453492637594607460361 * 10 ^ 70 +
        9646982642564521328624253415449908775340416610527361245847762354458505) : ℚ) := by
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

theorem recurrence5B2_coeff_37 :
    remainder6Coefficient2.coeff 37 =
      ((409531040105686179811852852632795946318969437598 * 10 ^ 70 +
        2224347764718549825403292007414347426920851139731202430164057069446112) : ℚ) := by
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

theorem recurrence5B2_coeff_38 :
    remainder6Coefficient2.coeff 38 =
      -((2103727689181521685240639785641295918936119616810 * 10 ^ 70 +
        7587317672988007377551061938968114508874337730440851367873362588842233) : ℚ) := by
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

theorem recurrence5B2_coeff_39 :
    remainder6Coefficient2.coeff 39 =
      ((10004238050043432322667300053791691047243806697359 * 10 ^ 70 +
        5949165150348148700514854396900521902689788492775075089991665584634156) : ℚ) := by
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

theorem recurrence5B2_coeff_40 :
    remainder6Coefficient2.coeff 40 =
      -((44121334114881333360394483400361858981006018046428 * 10 ^ 70 +
        0818063024131799764739975368002835894994686134274380108003702374298022) : ℚ) := by
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

theorem recurrence5B2_coeff_41 :
    remainder6Coefficient2.coeff 41 =
      ((180767145595180926651074668925377422038740103401226 * 10 ^ 70 +
        2793224855749032504344713388979204137388205143451079238376279404600459) : ℚ) := by
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

theorem recurrence5B2_coeff_42 :
    remainder6Coefficient2.coeff 42 =
      -((689116251037382606063793603095423553279416725476099 * 10 ^ 70 +
        5194072200053459078713521014567853374916980334960182620272811336787141) : ℚ) := by
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

theorem recurrence5B2_coeff_43 :
    remainder6Coefficient2.coeff 43 =
      ((2448077032854888501926091075380502418042398207160656 * 10 ^ 70 +
        4252072146224421226861236077632474486071631095597069438953024531528102) : ℚ) := by
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

theorem recurrence5B2_coeff_44 :
    remainder6Coefficient2.coeff 44 =
      -((8115925037485164662223429268773937047718679411064637 * 10 ^ 70 +
        8377776231471508861510830058346637651667916592983065650681196407054757) : ℚ) := by
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

theorem recurrence5B2_coeff_45 :
    remainder6Coefficient2.coeff 45 =
      ((25142993922891722766397951109449817359232711057872766 * 10 ^ 70 +
        5708111049877828195950679336250678287513206093934836198748761152708303) : ℚ) := by
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

theorem recurrence5B2_coeff_46 :
    remainder6Coefficient2.coeff 46 =
      -((72880949133725893757134617988905477772307267972747996 * 10 ^ 70 +
        4382488700464016912019862749077556815600353190554216542759103638802139) : ℚ) := by
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

theorem recurrence5B2_coeff_47 :
    remainder6Coefficient2.coeff 47 =
      ((197901448266798290397393966042779973722500169752707686 * 10 ^ 70 +
        4786460497191631303244248660732146794421498677905540617996101945954274) : ℚ) := by
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

theorem recurrence5B2_coeff_48 :
    remainder6Coefficient2.coeff 48 =
      -((503977144294736356143797564060744564264164805141482552 * 10 ^ 70 +
        8996995684993202113473453147617400067159708746278715596019363943667124) : ℚ) := by
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

theorem recurrence5B2_coeff_49 :
    remainder6Coefficient2.coeff 49 =
      ((1204922198331363797361679933882792473298788450228358830 * 10 ^ 70 +
        2928095085902031855383455309745085332083125673806345146629106310154192) : ℚ) := by
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

theorem recurrence5B2_coeff_50 :
    remainder6Coefficient2.coeff 50 =
      -((2707225311467136325810718745024939100075047821321300042 * 10 ^ 70 +
        9363253596572643771030821959144764513204297233297482293922234565416143) : ℚ) := by
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

theorem recurrence5B2_coeff_51 :
    remainder6Coefficient2.coeff 51 =
      ((5721509478874250720733094917263550907179345694749422277 * 10 ^ 70 +
        9723963635129840900885728775476451916594546070310157853735850185518867) : ℚ) := by
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

theorem recurrence5B2_coeff_52 :
    remainder6Coefficient2.coeff 52 =
      -((11384001148794245181120133242881174388790973208428901936 * 10 ^ 70 +
        3782775946305904742591335675799316286954180249072704011120817474508297) : ℚ) := by
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

theorem recurrence5B2_coeff_53 :
    remainder6Coefficient2.coeff 53 =
      ((21341709906385303719237549085296518653288853793770664718 * 10 ^ 70 +
        0060029302189312829528758224067390246612091213846827713190914423059271) : ℚ) := by
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

theorem recurrence5B2_coeff_54 :
    remainder6Coefficient2.coeff 54 =
      -((37726006108023352309313078629727776614749488512782950953 * 10 ^ 70 +
        8303647122388057366982675560359498188083913992715852778752631100251753) : ℚ) := by
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

theorem recurrence5B2_coeff_55 :
    remainder6Coefficient2.coeff 55 =
      ((62926476488565115189954925626914621334275564617815422017 * 10 ^ 70 +
        8205299852391534774144681002959689209136542158272314064161783610708783) : ℚ) := by
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

theorem recurrence5B2_coeff_56 :
    remainder6Coefficient2.coeff 56 =
      -((99103171209273101818755028711388020481457965892072268984 * 10 ^ 70 +
        1838332820467576950959857709542497892018113090962545432605529669121209) : ℚ) := by
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

theorem recurrence5B2_coeff_57 :
    remainder6Coefficient2.coeff 57 =
      ((147455641708439164723665948439717916966320744047224391162 * 10 ^ 70 +
        3637315950152209600631893306568726446046690153927320369762117224328709) : ℚ) := by
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

theorem recurrence5B2_coeff_58 :
    remainder6Coefficient2.coeff 58 =
      -((207391596944927796586954701287967005364279047862981387950 * 10 ^ 70 +
        4154142511534423737937416260198726165103961868893331538071563051752208) : ℚ) := by
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

theorem recurrence5B2_coeff_59 :
    remainder6Coefficient2.coeff 59 =
      ((275861762540726024918475037527311766609156271318421854787 * 10 ^ 70 +
        3837157911186009942191447285785282243598952701508974058064361631972566) : ℚ) := by
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

theorem recurrence5B2_coeff_60 :
    remainder6Coefficient2.coeff 60 =
      -((347180895007198679386789413382170494615162725648244865214 * 10 ^ 70 +
        4121030524219966644067891509948377339647605762826997679701536783249514) : ℚ) := by
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

theorem recurrence5B2_coeff_61 :
    remainder6Coefficient2.coeff 61 =
      ((413576876541405225263157841471003495639837113314240067656 * 10 ^ 70 +
        0915547120469019212902564693045179248833383288703424806542160724705545) : ℚ) := by
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

theorem recurrence5B2_coeff_62 :
    remainder6Coefficient2.coeff 62 =
      -((466491348877551465119635871587531369743315003419228366255 * 10 ^ 70 +
        2071293571680623540543493934046602176026922828480469944175079452281193) : ℚ) := by
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

theorem recurrence5B2_coeff_63 :
    remainder6Coefficient2.coeff 63 =
      ((498364154069955892140189317388514336613621075965539562423 * 10 ^ 70 +
        8256415373390042258397558817455378552625632716687896521641514818451944) : ℚ) := by
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

theorem recurrence5B2_coeff_64 :
    remainder6Coefficient2.coeff 64 =
      -((504396312810056801562505673248225271000620581185821027786 * 10 ^ 70 +
        5151153085593908332684529794541093692258520205065698723378259650621485) : ℚ) := by
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

theorem recurrence5B2_coeff_65 :
    remainder6Coefficient2.coeff 65 =
      ((483726674993870013738769307754077243255629042956958494781 * 10 ^ 70 +
        9455290325938692916708212435751130195267019016817291907137286988892052) : ℚ) := by
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

theorem recurrence5B2_coeff_66 :
    remainder6Coefficient2.coeff 66 =
      -((439626201979672564762357326509519267457093022433570739298 * 10 ^ 70 +
        3578193177700784472317566913875403756165673984158467524638574835520305) : ℚ) := by
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

theorem recurrence5B2_coeff_67 :
    remainder6Coefficient2.coeff 67 =
      ((378650712189037030703749051720802046605534074949005555542 * 10 ^ 70 +
        1493126733266137676861844376410955344084288285200825812741504730680119) : ℚ) := by
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

theorem recurrence5B2_coeff_68 :
    remainder6Coefficient2.coeff 68 =
      -((309052043175436139359360024642278286392869687106386095044 * 10 ^ 70 +
        2287228959420730188095671471706292103661197758485825045400395393603811) : ℚ) := by
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

theorem recurrence5B2_coeff_69 :
    remainder6Coefficient2.coeff 69 =
      ((238973474468591314151304481686249576856402646064416280809 * 10 ^ 70 +
        3345946568566464748832560604953380127886559726594087025422597051267284) : ℚ) := by
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

theorem recurrence5B2_coeff_70 :
    remainder6Coefficient2.coeff 70 =
      -((174963111270569295457137542741300765447471388703019159654 * 10 ^ 70 +
        8543357351415903945062301632816044862075014735274414684441584816386637) : ℚ) := by
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

theorem recurrence5B2_coeff_71 :
    remainder6Coefficient2.coeff 71 =
      ((121151621843523599214480429733654256449435620532226867321 * 10 ^ 70 +
        4697505657817687709664153430670350069444267653597135966732802330534219) : ℚ) := by
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

theorem recurrence5B2_coeff_72 :
    remainder6Coefficient2.coeff 72 =
      -((79164532702700689171259156602025454472472893573380734736 * 10 ^ 70 +
        7196616403425582099859272663967358190603379238719459552410162473522440) : ℚ) := by
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
