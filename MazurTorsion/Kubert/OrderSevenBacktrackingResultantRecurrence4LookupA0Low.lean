/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData4
import Mathlib.Tactic.NormNum

/-!
# Recurrence 4 lookup certificate: A0 source coefficients, low half

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence4A0_coeff_0 :
    remainder4Coefficient0.coeff 0 =
      (0 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_1 :
    remainder4Coefficient0.coeff 1 =
      (-480 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_2 :
    remainder4Coefficient0.coeff 2 =
      (-1155556 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_3 :
    remainder4Coefficient0.coeff 3 =
      (9736172392 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_4 :
    remainder4Coefficient0.coeff 4 =
      (-16423440806733 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_5 :
    remainder4Coefficient0.coeff 5 =
      (4962878559054749 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_6 :
    remainder4Coefficient0.coeff 6 =
      (102164852818091143 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_7 :
    remainder4Coefficient0.coeff 7 =
      (-174570283367325557914 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_8 :
    remainder4Coefficient0.coeff 8 =
      (16971635485316593160253 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_9 :
    remainder4Coefficient0.coeff 9 =
      (-1987372853128920730284497 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_10 :
    remainder4Coefficient0.coeff 10 =
      (1037153502365342951467098014 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_11 :
    remainder4Coefficient0.coeff 11 =
      (-349526738997984038153494449661 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_12 :
    remainder4Coefficient0.coeff 12 =
      (84901689992003848492177873655587 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_13 :
    remainder4Coefficient0.coeff 13 =
      (-16352667734463880226360448854219828 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_14 :
    remainder4Coefficient0.coeff 14 =
      (2565177297628097530010580556359543693 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_15 :
    remainder4Coefficient0.coeff 15 =
      (-333800508239121059175948637360295552192 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_16 :
    remainder4Coefficient0.coeff 16 =
      (36587384198255758979280741147876340582674 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_17 :
    remainder4Coefficient0.coeff 17 =
      (-3419412929303129369590936763792570525919843 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_18 :
    remainder4Coefficient0.coeff 18 =
      (275266221231594527722590210037775210341936415 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_19 :
    remainder4Coefficient0.coeff 19 =
      (-19254132146361394764594199340404152527817392416 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_20 :
    remainder4Coefficient0.coeff 20 =
      (1179191434858326803678139570533696562234113231007 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_21 :
    remainder4Coefficient0.coeff 21 =
      (-63662698240520829270727927863644116342844301394297 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_22 :
    remainder4Coefficient0.coeff 22 =
      (3048456799788126981426530242874006721063169129975568 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_23 :
    remainder4Coefficient0.coeff 23 =
      (-130190017247630784430273724525535800743183253852586767 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_24 :
    remainder4Coefficient0.coeff 24 =
      (4984012111357720919132972081171726882070498470418930825 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_25 :
    remainder4Coefficient0.coeff 25 =
      (-171833374329887690929979143920362797722934521553807165394 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_26 :
    remainder4Coefficient0.coeff 26 =
      (5358353641923289810316231454695640774731160930358869641301 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_27 :
    remainder4Coefficient0.coeff 27 =
      (-151733892613902320668731059276185396977874583181787529963366 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_28 :
    remainder4Coefficient0.coeff 28 =
      (3916261660788291569420069376764028379928785109835567828887690 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_29 :
    remainder4Coefficient0.coeff 29 =
      (-92448566200735918254424866746257832196092338994497115278176440 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_30 :
    remainder4Coefficient0.coeff 30 =
      (2002493030313663849759458446818828012981658913199308038612727636 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_31 :
    remainder4Coefficient0.coeff 31 =
      (-39920648526267385629952858400090707042200265355834615164512062208 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_32 :
    remainder4Coefficient0.coeff 32 =
      (734533177819509477287413271955281502005821078427064188360344442371 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_33 :
    remainder4Coefficient0.coeff 33 =
      (-12507452692977962651544595122820773459955498832237098200234945555742 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_34 :
    remainder4Coefficient0.coeff 34 =
      (197586420462991385248909542772129415135930036618213305292649025647133 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_35 :
    remainder4Coefficient0.coeff 35 =
      (-2902680805118970352871139647271194747604401551075543746504464144683328 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_36 :
    remainder4Coefficient0.coeff 36 =
      ((3 * 10 ^ 70 +
        9742882462546483249549056718894116011316711210031170589579524649197846) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_37 :
    remainder4Coefficient0.coeff 37 =
      -((50 * 10 ^ 70 +
        8213543483660942809957690511042854497063475878832254864470856856441634) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_38 :
    remainder4Coefficient0.coeff 38 =
      ((608 * 10 ^ 70 +
        1596189531773994598656774218130238755639278940312271766174398508850511) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_39 :
    remainder4Coefficient0.coeff 39 =
      -((6823 * 10 ^ 70 +
        1251170549194221430846048959370653224910873577491003681983242674804801) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_40 :
    remainder4Coefficient0.coeff 40 =
      ((71896 * 10 ^ 70 +
        6819966711527633191319997714427672769795222442919773561069858031147343) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_41 :
    remainder4Coefficient0.coeff 41 =
      -((712718 * 10 ^ 70 +
        0734788483776173122298590248485379690068318915160677312771485795258676) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_42 :
    remainder4Coefficient0.coeff 42 =
      ((6657247 * 10 ^ 70 +
        6318226452339400055634241503321154514772743610266037296127378929400351) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_43 :
    remainder4Coefficient0.coeff 43 =
      -((58679670 * 10 ^ 70 +
        1504962688268005975387631723641132508787499309238881208765493889823571) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_44 :
    remainder4Coefficient0.coeff 44 =
      ((488776435 * 10 ^ 70 +
        6956172415846479131359694355903840319106372781967595853558554161723593) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_45 :
    remainder4Coefficient0.coeff 45 =
      -((3852510585 * 10 ^ 70 +
        8048473692569738347169218738352833697880681990998305810053119145127830) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_46 :
    remainder4Coefficient0.coeff 46 =
      ((28769967559 * 10 ^ 70 +
        9817819811918013130383649950126923852107816831092272538441039427590772) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_47 :
    remainder4Coefficient0.coeff 47 =
      -((203807058938 * 10 ^ 70 +
        9069762039019664301648459371411587297439357768324093667918080645561781) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_48 :
    remainder4Coefficient0.coeff 48 =
      ((1371130542823 * 10 ^ 70 +
        1842150721098517967175393927491905839555583700223202166366631931175344) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_49 :
    remainder4Coefficient0.coeff 49 =
      -((8769768194628 * 10 ^ 70 +
        9105807251357786741769827395230528932397345372402484534391047643844940) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_50 :
    remainder4Coefficient0.coeff 50 =
      ((53381790827567 * 10 ^ 70 +
        4244154274601007747366021648075638082852107911194677131652075737508590) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_51 :
    remainder4Coefficient0.coeff 51 =
      -((309540294753858 * 10 ^ 70 +
        5033099372090542674237766588514053969279928818230534685864177133740893) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_52 :
    remainder4Coefficient0.coeff 52 =
      ((1711441805490243 * 10 ^ 70 +
        8397519695720582822022519525971149838281963279609161536387956405258181) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_53 :
    remainder4Coefficient0.coeff 53 =
      -((9030453049377010 * 10 ^ 70 +
        3620101117270949708545493980196735893640531383917728158851069683150107) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_54 :
    remainder4Coefficient0.coeff 54 =
      ((45511561886060662 * 10 ^ 70 +
        8553333617391812603464342608246166234748804523050039435189284774870618) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_55 :
    remainder4Coefficient0.coeff 55 =
      -((219251642291040787 * 10 ^ 70 +
        2546647733459784922820530093342100581728221553390189056035548213512656) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_56 :
    remainder4Coefficient0.coeff 56 =
      ((1010414829029634936 * 10 ^ 70 +
        2283908739166724087704574373383161256071197687769597165541031327709355) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_57 :
    remainder4Coefficient0.coeff 57 =
      -((4457616723382702318 * 10 ^ 70 +
        8518894610137196556102341442606011929362970079119588195173611977297505) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_58 :
    remainder4Coefficient0.coeff 58 =
      ((18838517245440986277 * 10 ^ 70 +
        5320928688992881194800991872511702208729285651243929385941262443449604) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_59 :
    remainder4Coefficient0.coeff 59 =
      -((76315313516479787827 * 10 ^ 70 +
        0487081249516218809357606793885905185697080587464127738372814506070245) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_60 :
    remainder4Coefficient0.coeff 60 =
      ((296526529348733163435 * 10 ^ 70 +
        6514481098165307147414227312137481883543218630922227684358011914044149) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_61 :
    remainder4Coefficient0.coeff 61 =
      -((1105744495845591294834 * 10 ^ 70 +
        3451132212385177366427028184281029405798960565992519866788614800313472) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_62 :
    remainder4Coefficient0.coeff 62 =
      ((3959360916770984161287 * 10 ^ 70 +
        5668367333964400645450168642981072450884470728478364009850981211642567) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_63 :
    remainder4Coefficient0.coeff 63 =
      -((13620780618649545980279 * 10 ^ 70 +
        8469776891798179807115206150951316824482253717518633592867227313520635) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_64 :
    remainder4Coefficient0.coeff 64 =
      ((45040315567274952965738 * 10 ^ 70 +
        8294970071399877035643832432403887454354070337430932295112130830313719) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_65 :
    remainder4Coefficient0.coeff 65 =
      -((143228097551643054824078 * 10 ^ 70 +
        7360685991333606995870890418040370088772968605232965571361190818481826) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_66 :
    remainder4Coefficient0.coeff 66 =
      ((438204356006963667507926 * 10 ^ 70 +
        1864273863292663309525678202294020243495815297457351575563856528955031) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_67 :
    remainder4Coefficient0.coeff 67 =
      -((1290419905869442014791300 * 10 ^ 70 +
        2055337689149965597070498041553523859646916044207133608455447943182640) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_68 :
    remainder4Coefficient0.coeff 68 =
      ((3659029743257642554173431 * 10 ^ 70 +
        3703542967885994882804159830157614429159295750921710533045770572200706) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_69 :
    remainder4Coefficient0.coeff 69 =
      -((9994172003593366337249813 * 10 ^ 70 +
        0393434495052939879097110689110456733259243015996342669675310581726471) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_70 :
    remainder4Coefficient0.coeff 70 =
      ((26304523612370033332620224 * 10 ^ 70 +
        1222276478139228171605858045872634574646230975847957516258788819253348) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_71 :
    remainder4Coefficient0.coeff 71 =
      -((66736779679105242612865764 * 10 ^ 70 +
        7397358923161793929807087608621757958188620872711622496208474733738499) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_72 :
    remainder4Coefficient0.coeff 72 =
      ((163264507017518134829938958 * 10 ^ 70 +
        6100282371851994185173758914013947766367631473503207541146652703706981) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_73 :
    remainder4Coefficient0.coeff 73 =
      -((385250397682266060202427579 * 10 ^ 70 +
        7396905920202973374952255110301229417905034462509235067536187545336222) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_74 :
    remainder4Coefficient0.coeff 74 =
      ((877091984276516223227301912 * 10 ^ 70 +
        4387112897031501232801110196746143832608541889317368905923470646429335) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_75 :
    remainder4Coefficient0.coeff 75 =
      -((1927157339764645003404952377 * 10 ^ 70 +
        4069805214443417921045820575471479795673355117669686817980778705336467) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_76 :
    remainder4Coefficient0.coeff 76 =
      ((4087635345459265407174635325 * 10 ^ 70 +
        2011761206551094466884283436548995692673741422330711364913473563022175) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_77 :
    remainder4Coefficient0.coeff 77 =
      -((8371766913620828787959910483 * 10 ^ 70 +
        5979783516743203546100704133730428311642677841407368228542824643915721) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_78 :
    remainder4Coefficient0.coeff 78 =
      ((16559748070657190043871716709 * 10 ^ 70 +
        2873868588425133217945142839705385257873302472610580920491864676236682) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_79 :
    remainder4Coefficient0.coeff 79 =
      -((31643063151446146386796436921 * 10 ^ 70 +
        1734007882908553377210873176861967450746453660487280130324779305991769) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_80 :
    remainder4Coefficient0.coeff 80 =
      ((58422955704673838967458698942 * 10 ^ 70 +
        5286503992202649592295700271467845383405589067730884314802796419221016) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_81 :
    remainder4Coefficient0.coeff 81 =
      -((104245350404801167085685149183 * 10 ^ 70 +
        6046783238729668669918728026912986730319386108799459887279014661430814) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_82 :
    remainder4Coefficient0.coeff 82 =
      ((179796993080558260279221420551 * 10 ^ 70 +
        9726183815259852306846432403121341581982543255244029577645818851102548) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_83 :
    remainder4Coefficient0.coeff 83 =
      -((299807251954072261914729804788 * 10 ^ 70 +
        2938088605495066869607672772121056283087993811986285799753660362653895) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_84 :
    remainder4Coefficient0.coeff 84 =
      ((483409145599314153751582281516 * 10 ^ 70 +
        8559116475769210647365984170274552135866004812089852982002266574616115) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_85 :
    remainder4Coefficient0.coeff 85 =
      -((753837843977681520130181780029 * 10 ^ 70 +
        5257363152098877430929499147574127452158415629080105222878627891864087) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_86 :
    remainder4Coefficient0.coeff 86 =
      ((1137123612057692598698166959408 * 10 ^ 70 +
        5091881950338239364148960747191751043145516771316495505414257686275768) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_87 :
    remainder4Coefficient0.coeff 87 =
      -((1659511180917703076843649613660 * 10 ^ 70 +
        1354035617988662097854306777358389486319929179861922897531904994712005) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_88 :
    remainder4Coefficient0.coeff 88 =
      ((2343538817729134368586086315801 * 10 ^ 70 +
        4217509406710843707448067969711269422730069772867397172527579584838613) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_89 :
    remainder4Coefficient0.coeff 89 =
      -((3203035692233677543034133103024 * 10 ^ 70 +
        1874977438200640368750943377662360960292298586530160463215722583094871) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_90 :
    remainder4Coefficient0.coeff 90 =
      ((4237694964683749202580834028176 * 10 ^ 70 +
        4096857003286494351749937598679970524384770531354898743124571380337277) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_91 :
    remainder4Coefficient0.coeff 91 =
      -((5428251177393272613659067103500 * 10 ^ 70 +
        2367731630701682637915427707867611227462934180490392126657667907456342) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_92 :
    remainder4Coefficient0.coeff 92 =
      ((6733501330921963449621335284059 * 10 ^ 70 +
        0831169268238333365854208720695242677616955345460937655564127570790800) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_93 :
    remainder4Coefficient0.coeff 93 =
      -((8090335925998022791172332624737 * 10 ^ 70 +
        5723645827954556020065494930868880071322246256098357069024863089937147) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_94 :
    remainder4Coefficient0.coeff 94 =
      ((9417526337652128650606095425680 * 10 ^ 70 +
        5252053637563917256893966150918698930726744782687970421882795126710194) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_95 :
    remainder4Coefficient0.coeff 95 =
      -((10623288182008538018950764289458 * 10 ^ 70 +
        2680511849680788815987080183305030182321984418912169171700587559320275) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_96 :
    remainder4Coefficient0.coeff 96 =
      ((11615761123617550949379524258951 * 10 ^ 70 +
        7880995149843237303543704997412073003272616028623079441523364974052631) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A0_coeff_97 :
    remainder4Coefficient0.coeff 97 =
      -((12314749793561964620939811485050 * 10 ^ 70 +
        2545943268794009388989703572599402961954287641389455918284558198443425) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
