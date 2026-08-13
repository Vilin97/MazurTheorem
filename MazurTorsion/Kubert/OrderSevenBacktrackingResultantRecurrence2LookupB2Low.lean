/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData2
import Mathlib.Tactic.NormNum

/-!
# Recurrence 2 lookup certificate: B2 source coefficients, low half

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence2B2_coeff_0 :
    remainder3Coefficient2.coeff 0 =
      (0 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_1 :
    remainder3Coefficient2.coeff 1 =
      (0 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_2 :
    remainder3Coefficient2.coeff 2 =
      (20566 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_3 :
    remainder3Coefficient2.coeff 3 =
      (467452502 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_4 :
    remainder3Coefficient2.coeff 4 =
      (-248803518198 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_5 :
    remainder3Coefficient2.coeff 5 =
      (383227126470131 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_6 :
    remainder3Coefficient2.coeff 6 =
      (-152822662923162884 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_7 :
    remainder3Coefficient2.coeff 7 =
      (42180852282813951032 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_8 :
    remainder3Coefficient2.coeff 8 =
      (-7051644585908704055280 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_9 :
    remainder3Coefficient2.coeff 9 =
      (789505055030491628391075 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_10 :
    remainder3Coefficient2.coeff 10 =
      (-59986525779113592452228114 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_11 :
    remainder3Coefficient2.coeff 11 =
      (3140523831275756399695569367 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_12 :
    remainder3Coefficient2.coeff 12 =
      (-114649868328970443430888145935 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_13 :
    remainder3Coefficient2.coeff 13 =
      (3145208853554043704377412826823 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_14 :
    remainder3Coefficient2.coeff 14 =
      (-95254075572483322850249961335294 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_15 :
    remainder3Coefficient2.coeff 15 =
      (4707286715224831131980976760272090 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_16 :
    remainder3Coefficient2.coeff 16 =
      (-252119760709282965148060859490098674 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_17 :
    remainder3Coefficient2.coeff 17 =
      (10920773607153928613786783012238872921 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_18 :
    remainder3Coefficient2.coeff 18 =
      (-374755433938771058464397696038142186056 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_19 :
    remainder3Coefficient2.coeff 19 =
      (10423139299556869835388904607584062679111 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_20 :
    remainder3Coefficient2.coeff 20 =
      (-236508744925100315692077438653052297791806 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_21 :
    remainder3Coefficient2.coeff 21 =
      (4264782476520433050173386942964682535047038 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_22 :
    remainder3Coefficient2.coeff 22 =
      (-55256619995110073203406178869402808396548740 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_23 :
    remainder3Coefficient2.coeff 23 =
      (285706806254928866062310198554674176338128828 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_24 :
    remainder3Coefficient2.coeff 24 =
      (9151218683896100753611859546553688315536346346 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_25 :
    remainder3Coefficient2.coeff 25 =
      (-360723793542344848926346348860010605221468898151 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_26 :
    remainder3Coefficient2.coeff 26 =
      (7988566775046323816950452536667043821428643273571 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_27 :
    remainder3Coefficient2.coeff 27 =
      (-135610457529676213927524080412967938276908000989499 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_28 :
    remainder3Coefficient2.coeff 28 =
      (1912098641510585058099084468722416136697822198628623 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_29 :
    remainder3Coefficient2.coeff 29 =
      (-23183387137118427190312349102213378182877449677860270 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_30 :
    remainder3Coefficient2.coeff 30 =
      (246329617178149273935393622793688400091367824947689466 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_31 :
    remainder3Coefficient2.coeff 31 =
      (-2321078854207125281928321165528633903884832772129450505 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_32 :
    remainder3Coefficient2.coeff 32 =
      (19554454400437866274729702375867507229487690725880338625 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_33 :
    remainder3Coefficient2.coeff 33 =
      (-148173271675304899089185520264698955187655856836240781529 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_34 :
    remainder3Coefficient2.coeff 34 =
      (1014337899014932756179294601359552920296855999551578100641 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_35 :
    remainder3Coefficient2.coeff 35 =
      (-6293016267641226930816983777632313952601640526445380151277 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_36 :
    remainder3Coefficient2.coeff 36 =
      (35453047198090537082304117523098262290953781713141305831790 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_37 :
    remainder3Coefficient2.coeff 37 =
      (-181499756823876778304060593417382305756426614026496891389935 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_38 :
    remainder3Coefficient2.coeff 38 =
      (843755290301089933115552025148303090521645311900760275574478 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_39 :
    remainder3Coefficient2.coeff 39 =
      (-3552824034029471684453840394271692866755848034950107359651480 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_40 :
    remainder3Coefficient2.coeff 40 =
      (13478123055651230228272777873715663363791103402982773920944516 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_41 :
    remainder3Coefficient2.coeff 41 =
      (-45582171189210250545017707180304950371503361684194561569665487 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_42 :
    remainder3Coefficient2.coeff 42 =
      (134429195558020180454399136591174639861549207080127987930005697 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_43 :
    remainder3Coefficient2.coeff 43 =
      (-328003938045700375173751495721136104332755576834768852631221653 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_44 :
    remainder3Coefficient2.coeff 44 =
      (557924028055441474238630776968822342538856427701636338978197629 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_45 :
    remainder3Coefficient2.coeff 45 =
      (4443215559487839326439914202816308765887547512828767566577894 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_46 :
    remainder3Coefficient2.coeff 46 =
      (-5190470250224262508551271917117761513256090003934359515937713572 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_47 :
    remainder3Coefficient2.coeff 47 =
      (28122045346581622831222804024479730765729259546789372377157070970 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_48 :
    remainder3Coefficient2.coeff 48 =
      (-106788653096648679148087335350647801913263895572835705266931236346 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_49 :
    remainder3Coefficient2.coeff 49 =
      (342145434390218184106531767714388496739031953827924299460661589676 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_50 :
    remainder3Coefficient2.coeff 50 =
      (-987235433873104535656362726172641254794587115864251552945804076105 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_51 :
    remainder3Coefficient2.coeff 51 =
      (2561901456258136949894791767672983359060878522867259312939165863923 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_52 :
    remainder3Coefficient2.coeff 52 =
      (-5457811960018399890535577784772290315877026020624914203761494109784 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_53 :
    remainder3Coefficient2.coeff 53 =
      (7209866222568054868512328548494855815959045172876543998169252113244 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_54 :
    remainder3Coefficient2.coeff 54 =
      (1724737831226548170000465792846091900982352387032329614998427719216 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_55 :
    remainder3Coefficient2.coeff 55 =
      (-13372367869848666839347703572120985123394727185653966147681404955432 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_56 :
    remainder3Coefficient2.coeff 56 =
      (-157339896768072354933942554862976313707979773239351019084456150604421 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_57 :
    remainder3Coefficient2.coeff 57 =
      (1159564890418055661323514297762148901433296114321838721244994297797577 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_58 :
    remainder3Coefficient2.coeff 58 =
      (-3054243963534027327407222692196537649633065226852682894389216541526680 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_59 :
    remainder3Coefficient2.coeff 59 =
      (-2858937352163103397112804505247217042729858885502902041365725400988923 : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_60 :
    remainder3Coefficient2.coeff 60 =
      ((5 * 10 ^ 70 +
        4534678257021364220065665885601967779032608595213555231118776038064568) : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_61 :
    remainder3Coefficient2.coeff 61 =
      -((20 * 10 ^ 70 +
        5316457637001890020694013735680233966638042633322734632182196570211985) : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_62 :
    remainder3Coefficient2.coeff 62 =
      ((23 * 10 ^ 70 +
        0619480194053390530218647033603763596156082753043918233161797927318675) : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_63 :
    remainder3Coefficient2.coeff 63 =
      ((143 * 10 ^ 70 +
        3322050784409541498630282889013093835565987124507123047930319437077533) : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_64 :
    remainder3Coefficient2.coeff 64 =
      -((900 * 10 ^ 70 +
        5447893521413281801840670945787098264834803571205293176637274299607663) : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_65 :
    remainder3Coefficient2.coeff 65 =
      ((2418 * 10 ^ 70 +
        7446152476167709049666999809968464537768999676262503271693769681195773) : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_66 :
    remainder3Coefficient2.coeff 66 =
      -((1219 * 10 ^ 70 +
        1726704762365575889116972647849103155504577598226140509866060555820458) : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_67 :
    remainder3Coefficient2.coeff 67 =
      -((19178 * 10 ^ 70 +
        2875446448841531236806362122177755799580882564598469929967208992738766) : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_68 :
    remainder3Coefficient2.coeff 68 =
      ((97482 * 10 ^ 70 +
        7413972977330840741571666419461094606328959665463097412149691014151041) : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_69 :
    remainder3Coefficient2.coeff 69 =
      -((255535 * 10 ^ 70 +
        2528096015106219807884752781334469308302588552952229209584596469340131) : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_70 :
    remainder3Coefficient2.coeff 70 =
      ((264267 * 10 ^ 70 +
        9044419317102424322353002264157586752254742401646693919167246904528533) : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_71 :
    remainder3Coefficient2.coeff 71 =
      ((1029960 * 10 ^ 70 +
        0007772281310642717885390182951937129250880590873228342112801682245293) : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_72 :
    remainder3Coefficient2.coeff 72 =
      -((6821433 * 10 ^ 70 +
        0578893228553685928493216088652583932457539998082710688173398952810092) : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B2_coeff_73 :
    remainder3Coefficient2.coeff 73 =
      ((22409306 * 10 ^ 70 +
        9522919787142159639007142043033037572457611885946470063852114368708480) : ℚ) := by
  unfold
    remainder3Coefficient2
    remainder3Coefficient2Block1
    remainder3Coefficient2Block0
    remainder3Coefficient2Chunk18
    remainder3Coefficient2Chunk17
    remainder3Coefficient2Chunk16
    remainder3Coefficient2Chunk15
    remainder3Coefficient2Chunk14
    remainder3Coefficient2Chunk13
    remainder3Coefficient2Chunk12
    remainder3Coefficient2Chunk11
    remainder3Coefficient2Chunk10
    remainder3Coefficient2Chunk9
    remainder3Coefficient2Chunk8
    remainder3Coefficient2Chunk7
    remainder3Coefficient2Chunk6
    remainder3Coefficient2Chunk5
    remainder3Coefficient2Chunk4
    remainder3Coefficient2Chunk3
    remainder3Coefficient2Chunk2
    remainder3Coefficient2Chunk1
    remainder3Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
