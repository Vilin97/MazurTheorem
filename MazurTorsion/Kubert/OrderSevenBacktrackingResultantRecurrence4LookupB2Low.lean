/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData4
import Mathlib.Tactic.NormNum

/-!
# Recurrence 4 lookup certificate: B2 source coefficients, low half

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence4B2_coeff_0 :
    remainder5Coefficient2.coeff 0 =
      (651676265583390656 : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_1 :
    remainder5Coefficient2.coeff 1 =
      (-3904316750011567564428 : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_2 :
    remainder5Coefficient2.coeff 2 =
      (5093903770579375179974528 : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_3 :
    remainder5Coefficient2.coeff 3 =
      (-1649953942590966925937924114 : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_4 :
    remainder5Coefficient2.coeff 4 =
      (795571214717754880505455628268 : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_5 :
    remainder5Coefficient2.coeff 5 =
      (-757559790066742260669737440496644 : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_6 :
    remainder5Coefficient2.coeff 6 =
      (268748139607748660204174231048393414 : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_7 :
    remainder5Coefficient2.coeff 7 =
      (52548553414629532693306633035720620121 : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_8 :
    remainder5Coefficient2.coeff 8 =
      (-79379899325181780253078158094622882830475 : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_9 :
    remainder5Coefficient2.coeff 9 =
      (32532065086379491853808401469825950953552628 : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_10 :
    remainder5Coefficient2.coeff 10 =
      (-7638890912177060890836355998085478710841642475 : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_11 :
    remainder5Coefficient2.coeff 11 =
      (1137526504219119908857042580441579458495760682684 : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_12 :
    remainder5Coefficient2.coeff 12 =
      (-101178186462559440121186921814030290761734516106294 : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_13 :
    remainder5Coefficient2.coeff 13 =
      (2379185042545648736766819599070891197835361784917466 : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_14 :
    remainder5Coefficient2.coeff 14 =
      (786183479401306607933074660720147105438538929445448164 : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_15 :
    remainder5Coefficient2.coeff 15 =
      (-146240481794592037497312872183826122870456310226440638140 : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_16 :
    remainder5Coefficient2.coeff 16 =
      (15248292486417181916145038731119252740424528550185793254729 : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_17 :
    remainder5Coefficient2.coeff 17 =
      (-1153050847284561192427896846738382619079941644461776748115589 : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_18 :
    remainder5Coefficient2.coeff 18 =
      (68258184381873605073543443106253861453016797280312861122182652 : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_19 :
    remainder5Coefficient2.coeff 19 =
      (-3277715656710412524663169147642284477795866187021559136508094854 : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_20 :
    remainder5Coefficient2.coeff 20 =
      (130211125860514281835901566322519233337728016826811275053504616878 : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_21 :
    remainder5Coefficient2.coeff 21 =
      (-4326368135038741439595326005605585911596955320739625826782538095391 : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_22 :
    remainder5Coefficient2.coeff 22 =
      (120686240136790556720623182219609045480772587261215924304388667361148 : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_23 :
    remainder5Coefficient2.coeff 23 =
      (-2812648938529590556619802321001536768531044382413144410826830335438135 : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_24 :
    remainder5Coefficient2.coeff 24 =
      ((5 * 10 ^ 70 +
        3625878708580417242433943240748179601805795298718588737548856443678977) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_25 :
    remainder5Coefficient2.coeff 25 =
      -((78 * 10 ^ 70 +
        4340088970730194866367079113948863730391169245469734222202437532827026) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_26 :
    remainder5Coefficient2.coeff 26 =
      ((671 * 10 ^ 70 +
        6100482695014821088497135835834770897053125034460347332106138331046799) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_27 :
    remainder5Coefficient2.coeff 27 =
      ((5360 * 10 ^ 70 +
        6800094290567322647116682415528722482981029148268669662047019653765462) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_28 :
    remainder5Coefficient2.coeff 28 =
      -((393731 * 10 ^ 70 +
        3707336141988997742466959905434240134898271575363261548613531158212504) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_29 :
    remainder5Coefficient2.coeff 29 =
      ((10708598 * 10 ^ 70 +
        4797650928247110118159056941613982537926038607106183398538199938682691) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_30 :
    remainder5Coefficient2.coeff 30 =
      -((215494668 * 10 ^ 70 +
        5506587377961901764180554649198091883272998655642802608400637721491036) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_31 :
    remainder5Coefficient2.coeff 31 =
      ((3607543772 * 10 ^ 70 +
        0381252641903967716514729648870302172247610925533987578083112664486253) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_32 :
    remainder5Coefficient2.coeff 32 =
      -((52517133007 * 10 ^ 70 +
        5692315026854207875757695230761066664209690181626496629554032185003315) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_33 :
    remainder5Coefficient2.coeff 33 =
      ((680048490274 * 10 ^ 70 +
        3735071683097265578953417144482668200102710731048712144385250345509695) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_34 :
    remainder5Coefficient2.coeff 34 =
      -((7941632772587 * 10 ^ 70 +
        2253146697798679491404522994654241282790865766915253558715128549573841) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_35 :
    remainder5Coefficient2.coeff 35 =
      ((84428650001058 * 10 ^ 70 +
        5542383267528288488752497252128823963187356609681971013889521130790039) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_36 :
    remainder5Coefficient2.coeff 36 =
      -((822796666141926 * 10 ^ 70 +
        1369937885619487389685219170370809357161388625724502697827027921435164) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_37 :
    remainder5Coefficient2.coeff 37 =
      ((7390489940400932 * 10 ^ 70 +
        3550014308267611312653323812874083302844971258924211157881399626893683) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_38 :
    remainder5Coefficient2.coeff 38 =
      -((61454176874452596 * 10 ^ 70 +
        3532249289194988239761266238355789116783272447143756982198563530322657) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_39 :
    remainder5Coefficient2.coeff 39 =
      ((474831318003330366 * 10 ^ 70 +
        6677184698920343257540216068164348820598620540427892523496985443744611) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_40 :
    remainder5Coefficient2.coeff 40 =
      -((3419967268121142796 * 10 ^ 70 +
        1081486082328413834764204671117466462476096937972333292757865308173539) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_41 :
    remainder5Coefficient2.coeff 41 =
      ((23025467468786996970 * 10 ^ 70 +
        9456175154186617880065289725511536971013502993327056838723833239344885) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_42 :
    remainder5Coefficient2.coeff 42 =
      -((145267245007742123734 * 10 ^ 70 +
        4361441613496547239508970513866131860820049684312465390020113721493365) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_43 :
    remainder5Coefficient2.coeff 43 =
      ((860701983671610967056 * 10 ^ 70 +
        4258237467202546168965401980225550612045440959140528789259174333939582) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_44 :
    remainder5Coefficient2.coeff 44 =
      -((4798651117566125098829 * 10 ^ 70 +
        1536326351389853687853317835415854359636878116891962121983868345438989) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_45 :
    remainder5Coefficient2.coeff 45 =
      ((25219588378537785911101 * 10 ^ 70 +
        8218857373156860187561585465932237209619053525712905522344182043434676) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_46 :
    remainder5Coefficient2.coeff 46 =
      -((125143010686210879918089 * 10 ^ 70 +
        8678846085804371350473274779775111173476699899353588722121928025927341) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_47 :
    remainder5Coefficient2.coeff 47 =
      ((587160368252486177697131 * 10 ^ 70 +
        1431380996008477547719676886862934876389339746596699377824349593675430) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_48 :
    remainder5Coefficient2.coeff 48 =
      -((2608322246740818674633953 * 10 ^ 70 +
        9941366911775449147619930209973610712011424265786577937782213173095032) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_49 :
    remainder5Coefficient2.coeff 49 =
      ((10983472566203357853310194 * 10 ^ 70 +
        3352735667181074857215680445776814980056719336933955341374120168908765) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_50 :
    remainder5Coefficient2.coeff 50 =
      -((43889738893697888849049941 * 10 ^ 70 +
        4628930848294568881657626603276068273290098651060279256736447572493963) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_51 :
    remainder5Coefficient2.coeff 51 =
      ((166593408122492983949038106 * 10 ^ 70 +
        8122708792977361567383422554617558162626861787462679029859526032574294) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_52 :
    remainder5Coefficient2.coeff 52 =
      -((601187507045704043526090236 * 10 ^ 70 +
        1949229710423010243260962345466744752111913901373716277087590752698764) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_53 :
    remainder5Coefficient2.coeff 53 =
      ((2064275839240507432282761360 * 10 ^ 70 +
        5818940945953748592775308033940543929208064654046348673762068662810595) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_54 :
    remainder5Coefficient2.coeff 54 =
      -((6749085101777891110996492264 * 10 ^ 70 +
        3893057275104394320871879394892358327851883502617071328492625121459716) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_55 :
    remainder5Coefficient2.coeff 55 =
      ((21024382172476823291333063939 * 10 ^ 70 +
        4672342583733747956800340751816982395504265507116055743330649135555902) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_56 :
    remainder5Coefficient2.coeff 56 =
      -((62438846032158517704049171670 * 10 ^ 70 +
        0868494143884183472150626839566604869802198225054034248152829434782794) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_57 :
    remainder5Coefficient2.coeff 57 =
      ((176874127641426313703373225797 * 10 ^ 70 +
        5558728590449554321326121383737442730767825687823141880777478249245274) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_58 :
    remainder5Coefficient2.coeff 58 =
      -((478134719723108710836609905641 * 10 ^ 70 +
        9899913479650921489243010353121852120210903954166500719471170047761633) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_59 :
    remainder5Coefficient2.coeff 59 =
      ((1233920453440663732157465389047 * 10 ^ 70 +
        4875268480870654859879803253631462811396693144240801215664763511930056) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_60 :
    remainder5Coefficient2.coeff 60 =
      -((3041068607623164921631358504367 * 10 ^ 70 +
        9006988115774766001933856949116843756243670105440930637964532332193094) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_61 :
    remainder5Coefficient2.coeff 61 =
      ((7159727272219938722640580178810 * 10 ^ 70 +
        9230895991687462477646958561316688165742328549755770011258873459101570) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_62 :
    remainder5Coefficient2.coeff 62 =
      -((16106653750531272580204760374185 * 10 ^ 70 +
        5687933077295684837139437188650072929313857455038601095929319568360822) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_63 :
    remainder5Coefficient2.coeff 63 =
      ((34628898647837603484806932119158 * 10 ^ 70 +
        1518702623142179769831123086955917965572169334556488616772112413493718) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_64 :
    remainder5Coefficient2.coeff 64 =
      -((71164083425035438686871250976953 * 10 ^ 70 +
        6142747007291482446764896327637453744587471512989289770221064068708243) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_65 :
    remainder5Coefficient2.coeff 65 =
      ((139802175790552342054296264711958 * 10 ^ 70 +
        6764628892198754854963538434937951225861033084528296682989515273864412) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_66 :
    remainder5Coefficient2.coeff 66 =
      -((262552745926616556641542231511944 * 10 ^ 70 +
        1292345485823440329360740611072879209531122923307068852953974004696743) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_67 :
    remainder5Coefficient2.coeff 67 =
      ((471370360596554978358070586011271 * 10 ^ 70 +
        0847841740224289086005796543650471316445176151528692546371058258914689) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_68 :
    remainder5Coefficient2.coeff 68 =
      -((808940975629059665662139601311155 * 10 ^ 70 +
        8992813342920912128196921078229703492729129234257674013304324521058101) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_69 :
    remainder5Coefficient2.coeff 69 =
      ((1326828399584128846854692684185114 * 10 ^ 70 +
        3265232326407096440602477260961578959115362666201293028457150846054336) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_70 :
    remainder5Coefficient2.coeff 70 =
      -((2079478250260570660548190148918241 * 10 ^ 70 +
        4061452722080672530768976560481190980900061449939120266106489299917303) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_71 :
    remainder5Coefficient2.coeff 71 =
      ((3113086590544124092333828149385047 * 10 ^ 70 +
        2872532012724567009534138779567505873644747963921521905738484982492975) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_72 :
    remainder5Coefficient2.coeff 72 =
      -((4449678943384358055276361386941395 * 10 ^ 70 +
        5720026517494472625372653272198640283108271669315286186730863301887801) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_73 :
    remainder5Coefficient2.coeff 73 =
      ((6068836639659817783353098983834720 * 10 ^ 70 +
        1241164025084094431048307875525275415896651818165674449271299739273166) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_74 :
    remainder5Coefficient2.coeff 74 =
      -((7891820587525188565581898251881977 * 10 ^ 70 +
        0700717212473828031076378084737000364156596211677480211291914529408303) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_75 :
    remainder5Coefficient2.coeff 75 =
      ((9774407261503846186066833504800445 * 10 ^ 70 +
        2470188828046459055095288469815490854009907252886542379241341557170580) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_76 :
    remainder5Coefficient2.coeff 76 =
      -((11514452332111669998914171608060949 * 10 ^ 70 +
        7111831232225463660673273907143356151531158108130327072332823232325881) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_77 :
    remainder5Coefficient2.coeff 77 =
      ((12877314131718046685321323374377921 * 10 ^ 70 +
        7835217858856667967098033242671384373762674067872601378107818909339621) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_78 :
    remainder5Coefficient2.coeff 78 =
      -((13637049275983123526416106364825534 * 10 ^ 70 +
        5571445851015848956938867083371661836479116302742408090896820233112375) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_79 :
    remainder5Coefficient2.coeff 79 =
      ((13625208987494172389839358675065467 * 10 ^ 70 +
        6343307782759518624250686422817615530570004539378932731114853091626257) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_80 :
    remainder5Coefficient2.coeff 80 =
      -((12774477868872078770496080714719971 * 10 ^ 70 +
        7463906087883508248205876316241921840851320442123902806804727691656654) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_81 :
    remainder5Coefficient2.coeff 81 =
      ((11143616245134050984850639521813302 * 10 ^ 70 +
        8911161634928558279121047336448476057851156252472751373750385947328566) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_82 :
    remainder5Coefficient2.coeff 82 =
      -((8914280116848690864359806800484255 * 10 ^ 70 +
        2203878506415793455783729792458513207132800211159914855346056823564522) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_83 :
    remainder5Coefficient2.coeff 83 =
      ((6358381435836985426820898238016912 * 10 ^ 70 +
        9846063276244013636825165295549155804687678200437528652829898784519866) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B2_coeff_84 :
    remainder5Coefficient2.coeff 84 =
      -((3783919235287082799367635333006711 * 10 ^ 70 +
        7817976646411081427391618219076593506964666191688760857017444128470589) : ℚ) := by
  unfold
    remainder5Coefficient2
    remainder5Coefficient2Block1
    remainder5Coefficient2Block0
    remainder5Coefficient2Chunk21
    remainder5Coefficient2Chunk20
    remainder5Coefficient2Chunk19
    remainder5Coefficient2Chunk18
    remainder5Coefficient2Chunk17
    remainder5Coefficient2Chunk16
    remainder5Coefficient2Chunk15
    remainder5Coefficient2Chunk14
    remainder5Coefficient2Chunk13
    remainder5Coefficient2Chunk12
    remainder5Coefficient2Chunk11
    remainder5Coefficient2Chunk10
    remainder5Coefficient2Chunk9
    remainder5Coefficient2Chunk8
    remainder5Coefficient2Chunk7
    remainder5Coefficient2Chunk6
    remainder5Coefficient2Chunk5
    remainder5Coefficient2Chunk4
    remainder5Coefficient2Chunk3
    remainder5Coefficient2Chunk2
    remainder5Coefficient2Chunk1
    remainder5Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
