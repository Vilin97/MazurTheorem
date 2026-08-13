/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData2
import Mathlib.Tactic.NormNum

/-!
# Recurrence 2 lookup certificate: C0 source coefficients, low half

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence2C0_coeff_0 :
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

theorem recurrence2C0_coeff_1 :
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

theorem recurrence2C0_coeff_2 :
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

theorem recurrence2C0_coeff_3 :
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

theorem recurrence2C0_coeff_4 :
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

theorem recurrence2C0_coeff_5 :
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

theorem recurrence2C0_coeff_6 :
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

theorem recurrence2C0_coeff_7 :
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

theorem recurrence2C0_coeff_8 :
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

theorem recurrence2C0_coeff_9 :
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

theorem recurrence2C0_coeff_10 :
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

theorem recurrence2C0_coeff_11 :
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

theorem recurrence2C0_coeff_12 :
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

theorem recurrence2C0_coeff_13 :
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

theorem recurrence2C0_coeff_14 :
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

theorem recurrence2C0_coeff_15 :
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

theorem recurrence2C0_coeff_16 :
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

theorem recurrence2C0_coeff_17 :
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

theorem recurrence2C0_coeff_18 :
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

theorem recurrence2C0_coeff_19 :
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

theorem recurrence2C0_coeff_20 :
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

theorem recurrence2C0_coeff_21 :
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

theorem recurrence2C0_coeff_22 :
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

theorem recurrence2C0_coeff_23 :
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

theorem recurrence2C0_coeff_24 :
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

theorem recurrence2C0_coeff_25 :
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

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
