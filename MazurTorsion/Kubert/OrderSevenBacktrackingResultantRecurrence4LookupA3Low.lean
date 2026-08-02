/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData4
import Mathlib.Tactic.NormNum

/-!
# Recurrence 4 lookup certificate: A3 source coefficients, low half

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence4A3_coeff_0 :
    remainder4Coefficient3.coeff 0 =
      (-7616 : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_1 :
    remainder4Coefficient3.coeff 1 =
      (23629396 : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_2 :
    remainder4Coefficient3.coeff 2 =
      (58932891758 : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_3 :
    remainder4Coefficient3.coeff 3 =
      (-101789216513848 : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_4 :
    remainder4Coefficient3.coeff 4 =
      (24905087386651268 : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_5 :
    remainder4Coefficient3.coeff 5 =
      (2001081781821722943 : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_6 :
    remainder4Coefficient3.coeff 6 =
      (-667056002337536511217 : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_7 :
    remainder4Coefficient3.coeff 7 =
      (-77234185748797243479815 : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_8 :
    remainder4Coefficient3.coeff 8 =
      (64020759979726943306282040 : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_9 :
    remainder4Coefficient3.coeff 9 =
      (-25288748029848523739897038488 : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_10 :
    remainder4Coefficient3.coeff 10 =
      (7300343282146366199862564940260 : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_11 :
    remainder4Coefficient3.coeff 11 =
      (-1604983998422124665226856786580890 : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_12 :
    remainder4Coefficient3.coeff 12 =
      (280063413607009459944662920136899040 : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_13 :
    remainder4Coefficient3.coeff 13 =
      (-39836705852626321198484094015320186719 : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_14 :
    remainder4Coefficient3.coeff 14 =
      (4705699001915517302227575987346835340291 : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_15 :
    remainder4Coefficient3.coeff 15 =
      (-468462320210055742493123276582195904343317 : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_16 :
    remainder4Coefficient3.coeff 16 =
      (39783714118134389111331084075750880162985953 : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_17 :
    remainder4Coefficient3.coeff 17 =
      (-2911841972879974303016806756728570199616202077 : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_18 :
    remainder4Coefficient3.coeff 18 =
      (185314130585738044570745419712469338945444236050 : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_19 :
    remainder4Coefficient3.coeff 19 =
      (-10334918482420387545971834870050575452476132688008 : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_20 :
    remainder4Coefficient3.coeff 20 =
      (508591730138059299965846106018491097105069144624610 : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_21 :
    remainder4Coefficient3.coeff 21 =
      (-22222586450892042949714855548866906170527911350885778 : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_22 :
    remainder4Coefficient3.coeff 22 =
      (867013210352089439619037112221710776892657448685279619 : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_23 :
    remainder4Coefficient3.coeff 23 =
      (-30358970081220483053746604020669295849210977010557373990 : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_24 :
    remainder4Coefficient3.coeff 24 =
      (958549932918181534168698458367991162511273384123683668925 : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_25 :
    remainder4Coefficient3.coeff 25 =
      (-27408224837271437607113020452955629138896453848291157807357 : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_26 :
    remainder4Coefficient3.coeff 26 =
      (712546452039532100343877008622930485719273277740471821354561 : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_27 :
    remainder4Coefficient3.coeff 27 =
      (-16904840327259068167910287415613687228127951366770675663137123 : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_28 :
    remainder4Coefficient3.coeff 28 =
      (367248148725530123287379405094893962092224422107284683991055190 : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_29 :
    remainder4Coefficient3.coeff 29 =
      (-7328936256050768257442442385040526539912647330781583192183234343 : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_30 :
    remainder4Coefficient3.coeff 30 =
      (134754790433530815027688277849096376546478491198475048344833764475 : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_31 :
    remainder4Coefficient3.coeff 31 =
      (-2289149482085260253403876502309858107748901235349124368436987881648 : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_32 :
    remainder4Coefficient3.coeff 32 =
      (36021229464291217989389134979735591213549505133352803754096776485647 : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_33 :
    remainder4Coefficient3.coeff 33 =
      (-526325834255430488728353153076527252153101129986627852491429014375454 : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_34 :
    remainder4Coefficient3.coeff 34 =
      (7157400131119243975030359253826818341912189462149261973259840327566624 : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_35 :
    remainder4Coefficient3.coeff 35 =
      -((9 * 10 ^ 70 +
        0780693227907727741706804856687061065684925243940551419908147830810647) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_36 :
    remainder4Coefficient3.coeff 36 =
      ((107 * 10 ^ 70 +
        6087137600442387103020668378959092243060557998844135318561096240782175) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_37 :
    remainder4Coefficient3.coeff 37 =
      -((1194 * 10 ^ 70 +
        3851926644693827928561150135540377093440353256382488385316957806029989) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_38 :
    remainder4Coefficient3.coeff 38 =
      ((12435 * 10 ^ 70 +
        5353316209464298652411339259684633616148416377578518477590756372369666) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_39 :
    remainder4Coefficient3.coeff 39 =
      -((121658 * 10 ^ 70 +
        8981461377356276118894252080253034951418050688051876615714839546903304) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_40 :
    remainder4Coefficient3.coeff 40 =
      ((1120154 * 10 ^ 70 +
        5700006657874512750042443660160551344288227222878660602085264462141303) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_41 :
    remainder4Coefficient3.coeff 41 =
      -((9721291 * 10 ^ 70 +
        7874385236989461213995153192849912266323621442347552791987033814011373) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_42 :
    remainder4Coefficient3.coeff 42 =
      ((79634932 * 10 ^ 70 +
        8812669157617274692546069445170591879432976287010545566441611160454230) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_43 :
    remainder4Coefficient3.coeff 43 =
      -((616602437 * 10 ^ 70 +
        2971021994548258522205209363837801466519201862219578863345484230057377) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_44 :
    remainder4Coefficient3.coeff 44 =
      ((4518413712 * 10 ^ 70 +
        1782037323462868241125242081914160804237194876588248734113168526624428) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_45 :
    remainder4Coefficient3.coeff 45 =
      -((31374279953 * 10 ^ 70 +
        3398932986127055903753407290844111818219232994146154981264266312084289) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_46 :
    remainder4Coefficient3.coeff 46 =
      ((206665955018 * 10 ^ 70 +
        9853123910196592861971301502374650733395637270963552577659336064834752) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_47 :
    remainder4Coefficient3.coeff 47 =
      -((1292843691442 * 10 ^ 70 +
        3443747586447538365589461029069585544298145161513284882836310635406040) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_48 :
    remainder4Coefficient3.coeff 48 =
      ((7688739840799 * 10 ^ 70 +
        4062450600520925749578666725908320006586536194710238267178603437126487) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_49 :
    remainder4Coefficient3.coeff 49 =
      -((43513455148816 * 10 ^ 70 +
        0138808008960436624962849771065693365379653972588730664017346990750967) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_50 :
    remainder4Coefficient3.coeff 50 =
      ((234561512742118 * 10 ^ 70 +
        7797357872467025137267397853104724282502673068013864112946545200812482) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_51 :
    remainder4Coefficient3.coeff 51 =
      -((1205423822336854 * 10 ^ 70 +
        3688341955214657759705056771932106625902570291914474503900926639874603) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_52 :
    remainder4Coefficient3.coeff 52 =
      ((5910691684737118 * 10 ^ 70 +
        1490537238395383521573549331045772415807717606142427311272445541711955) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_53 :
    remainder4Coefficient3.coeff 53 =
      -((27675770395183778 * 10 ^ 70 +
        3417625360114089375915156499542446039001454108000008832128672540437435) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_54 :
    remainder4Coefficient3.coeff 54 =
      ((123838017802424772 * 10 ^ 70 +
        2285128813620963137533327495660058940106978905370184931473429801454087) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_55 :
    remainder4Coefficient3.coeff 55 =
      -((529925266289348895 * 10 ^ 70 +
        3182188329646959484967787993984372253939286647903329211287559533338841) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_56 :
    remainder4Coefficient3.coeff 56 =
      ((2170098630242407913 * 10 ^ 70 +
        7294415269457435219252305979344240371389484534184419706849732858757275) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_57 :
    remainder4Coefficient3.coeff 57 =
      -((8510038022267733582 * 10 ^ 70 +
        6487345205969852514902265145721357265400467885648246742563974307760266) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_58 :
    remainder4Coefficient3.coeff 58 =
      ((31977132843479892915 * 10 ^ 70 +
        7198707630552023701634044314024800333800286926291578203891849610886569) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_59 :
    remainder4Coefficient3.coeff 59 =
      -((115201692446233855399 * 10 ^ 70 +
        1690070432355271286941235790070175854008216454197867367866776431540214) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_60 :
    remainder4Coefficient3.coeff 60 =
      ((398136487191221237606 * 10 ^ 70 +
        6248891098841594697251302002750330752116229148176061210136909063789274) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_61 :
    remainder4Coefficient3.coeff 61 =
      -((1320654071156342915753 * 10 ^ 70 +
        2377930498554300320615213173474873462479074392759662961033464828791656) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_62 :
    remainder4Coefficient3.coeff 62 =
      ((4206768424231584262923 * 10 ^ 70 +
        9608450429898959935770937424979281004994028722787094532067595877950555) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_63 :
    remainder4Coefficient3.coeff 63 =
      -((12874127932169583448986 * 10 ^ 70 +
        8229589983169199308679175431201465069901293581379721389509758176396370) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_64 :
    remainder4Coefficient3.coeff 64 =
      ((37869818901217598590214 * 10 ^ 70 +
        2684189650113752618990603588130000367168724536285271053293315781893240) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_65 :
    remainder4Coefficient3.coeff 65 =
      -((107117652372300457653530 * 10 ^ 70 +
        2820438646931477662914417804416016743264598496496376644293653595881791) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_66 :
    remainder4Coefficient3.coeff 66 =
      ((291472520655757624173293 * 10 ^ 70 +
        9318407221502233772779373922960807076604420762370008498635745436062436) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_67 :
    remainder4Coefficient3.coeff 67 =
      -((763255251261824813446920 * 10 ^ 70 +
        0663392015126849047088005903228127894112915849723930040310267243534773) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_68 :
    remainder4Coefficient3.coeff 68 =
      ((1924134123708768457970621 * 10 ^ 70 +
        3858766004763946451059514069998257159151086156477369369904758035586916) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_69 :
    remainder4Coefficient3.coeff 69 =
      -((4671358596863882506937197 * 10 ^ 70 +
        4607530141062994742416789604742585907951309682530483772473407079150256) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_70 :
    remainder4Coefficient3.coeff 70 =
      ((10925313582757997447119037 * 10 ^ 70 +
        1203173760456059708058576033981709342934246155642205223674264748246070) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_71 :
    remainder4Coefficient3.coeff 71 =
      -((24622934642878660593157367 * 10 ^ 70 +
        3357171702151507033194275056968014187668490157672808431725030659478844) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_72 :
    remainder4Coefficient3.coeff 72 =
      ((53491576224476315570591120 * 10 ^ 70 +
        7616078311043927508073497568813104240899397053739775261472170319418578) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_73 :
    remainder4Coefficient3.coeff 73 =
      -((112043723397455956258232126 * 10 ^ 70 +
        7733157513605233991939355882333685459730009074923019445965198858005588) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_74 :
    remainder4Coefficient3.coeff 74 =
      ((226337091364494966347794659 * 10 ^ 70 +
        1502277746545911310307221472340018277559597428174046746526451661084661) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_75 :
    remainder4Coefficient3.coeff 75 =
      -((441054601901686700619299692 * 10 ^ 70 +
        1724347500140079239516180910028795188100506364583632783297769581582843) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_76 :
    remainder4Coefficient3.coeff 76 =
      ((829264093409921641203331198 * 10 ^ 70 +
        2631361253669475146952727960264173445943913949256711140820590999958711) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_77 :
    remainder4Coefficient3.coeff 77 =
      -((1504686293150239720538056545 * 10 ^ 70 +
        0673279847508665206965539321043334579609782446054165238406422987935828) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_78 :
    remainder4Coefficient3.coeff 78 =
      ((2635323034131858622864248028 * 10 ^ 70 +
        1160865291812191698700183030407192593425287303006320852572963120867419) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_79 :
    remainder4Coefficient3.coeff 79 =
      -((4455868535293460241289148536 * 10 ^ 70 +
        9056962650126648688109729548551190686680552259888223124808147527714126) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_80 :
    remainder4Coefficient3.coeff 80 =
      ((7274633662313967423976710516 * 10 ^ 70 +
        6516859814540005554852213480715214336394056292484245374552224658963018) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_81 :
    remainder4Coefficient3.coeff 81 =
      -((11469215614884445157030799907 * 10 ^ 70 +
        5071724930974058515006252029554182229322469277554972107165099342701197) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_82 :
    remainder4Coefficient3.coeff 82 =
      ((17464566618595354816947065542 * 10 ^ 70 +
        0389043829981722676166583905580549629734913501976491534271568877345444) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_83 :
    remainder4Coefficient3.coeff 83 =
      -((25688297043961157740869759420 * 10 ^ 70 +
        1837509490473555219552360296395708279183349155109405322342660980891147) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_84 :
    remainder4Coefficient3.coeff 84 =
      ((36501647278996069549443593797 * 10 ^ 70 +
        9459564800358228253967084647499925554901632789004196578234884521360594) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_85 :
    remainder4Coefficient3.coeff 85 =
      -((50110641123168082716766158500 * 10 ^ 70 +
        9014461038714557812331053718913445477112391705587955989794091414765793) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_86 :
    remainder4Coefficient3.coeff 86 =
      ((66469598171426207587588527273 * 10 ^ 70 +
        5553047847158229315562194407793096608740892655211345026805121398781099) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_87 :
    remainder4Coefficient3.coeff 87 =
      -((85196479599277902758016711398 * 10 ^ 70 +
        8640214830215079889260459041437774369742629957332327091327787831340584) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_88 :
    remainder4Coefficient3.coeff 88 =
      ((105523791107890834557777531798 * 10 ^ 70 +
        9703648770617045396882137448897179689092220569267028088911957491445320) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_89 :
    remainder4Coefficient3.coeff 89 =
      -((126307374817510221291726220219 * 10 ^ 70 +
        9909324262182354980719504978326965469372748881127582823873908530577747) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_90 :
    remainder4Coefficient3.coeff 90 =
      ((146106973995793965173726715424 * 10 ^ 70 +
        4778894440889510909997659030272716539324801399583469113074395479516212) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A3_coeff_91 :
    remainder4Coefficient3.coeff 91 =
      -((163337672718356691756719939335 * 10 ^ 70 +
        9265976049075004945941217714524057724774255021178445864100388080550674) : ℚ) := by
  unfold
    remainder4Coefficient3
    remainder4Coefficient3Block1
    remainder4Coefficient3Block0
    remainder4Coefficient3Chunk22
    remainder4Coefficient3Chunk21
    remainder4Coefficient3Chunk20
    remainder4Coefficient3Chunk19
    remainder4Coefficient3Chunk18
    remainder4Coefficient3Chunk17
    remainder4Coefficient3Chunk16
    remainder4Coefficient3Chunk15
    remainder4Coefficient3Chunk14
    remainder4Coefficient3Chunk13
    remainder4Coefficient3Chunk12
    remainder4Coefficient3Chunk11
    remainder4Coefficient3Chunk10
    remainder4Coefficient3Chunk9
    remainder4Coefficient3Chunk8
    remainder4Coefficient3Chunk7
    remainder4Coefficient3Chunk6
    remainder4Coefficient3Chunk5
    remainder4Coefficient3Chunk4
    remainder4Coefficient3Chunk3
    remainder4Coefficient3Chunk2
    remainder4Coefficient3Chunk1
    remainder4Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
