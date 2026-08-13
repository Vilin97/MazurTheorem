/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData4
import Mathlib.Tactic.NormNum

/-!
# Recurrence 4 lookup certificate: A4 source coefficients, low half

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence4A4_coeff_0 :
    remainder4Coefficient4.coeff 0 =
      (-384736 : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_1 :
    remainder4Coefficient4.coeff 1 =
      (556020644 : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_2 :
    remainder4Coefficient4.coeff 2 =
      (860860911458 : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_3 :
    remainder4Coefficient4.coeff 3 =
      (-987926129188182 : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_4 :
    remainder4Coefficient4.coeff 4 =
      (140675585138572631 : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_5 :
    remainder4Coefficient4.coeff 5 =
      (20151219772032322722 : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_6 :
    remainder4Coefficient4.coeff 6 =
      (-2438654708488280028551 : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_7 :
    remainder4Coefficient4.coeff 7 =
      (-553594068115153391367507 : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_8 :
    remainder4Coefficient4.coeff 8 =
      (250410476581740108401049598 : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_9 :
    remainder4Coefficient4.coeff 9 =
      (-81352128705906514960143558313 : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_10 :
    remainder4Coefficient4.coeff 10 =
      (20259837629907699206396766838382 : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_11 :
    remainder4Coefficient4.coeff 11 =
      (-3915823094088946880177830648985549 : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_12 :
    remainder4Coefficient4.coeff 12 =
      (609222704994768969809439283247736730 : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_13 :
    remainder4Coefficient4.coeff 13 =
      (-78019593595669326978467154188316895773 : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_14 :
    remainder4Coefficient4.coeff 14 =
      (8358933071370862864202832960999674154190 : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_15 :
    remainder4Coefficient4.coeff 15 =
      (-759305252792864792433701417611944011339664 : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_16 :
    remainder4Coefficient4.coeff 16 =
      (59135356874047274919093183023644990176958476 : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_17 :
    remainder4Coefficient4.coeff 17 =
      (-3986415948365885401007649546959463265647367604 : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_18 :
    remainder4Coefficient4.coeff 18 =
      (234548062879281292593247267168296247595866904685 : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_19 :
    remainder4Coefficient4.coeff 19 =
      (-12133524745625283729717569456466532112506261960103 : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_20 :
    remainder4Coefficient4.coeff 20 =
      (555521874147057891042828740360306050857986744757232 : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_21 :
    remainder4Coefficient4.coeff 21 =
      (-22643651908146602027659245862682130140162172631007072 : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_22 :
    remainder4Coefficient4.coeff 22 =
      (826147545813881830538254359649742630432773948279396433 : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_23 :
    remainder4Coefficient4.coeff 23 =
      (-27112274718196394885972448403258543727069845245422232830 : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_24 :
    remainder4Coefficient4.coeff 24 =
      (803945236426458360854932137167489557430696893798142028543 : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_25 :
    remainder4Coefficient4.coeff 25 =
      (-21629157518737420483674560023201587716100636682098169625936 : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_26 :
    remainder4Coefficient4.coeff 26 =
      (529991947620463645574003008043512019857708150709628587283563 : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_27 :
    remainder4Coefficient4.coeff 27 =
      (-11870193405757571851594786880528523288659666673869140466403093 : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_28 :
    remainder4Coefficient4.coeff 28 =
      (243802724226128588316838162848955966904405137961048691693306934 : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_29 :
    remainder4Coefficient4.coeff 29 =
      (-4606241927433366204370312450758512982358834085100377992982461734 : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_30 :
    remainder4Coefficient4.coeff 30 =
      (80283932389129692368636065087460391814795439138607761311750108190 : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_31 :
    remainder4Coefficient4.coeff 31 =
      (-1294343677823700308666563326187316069946451188904251807215487403418 : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_32 :
    remainder4Coefficient4.coeff 32 =
      (19350899117018021095469345400462618167083980859107511636263763358237 : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_33 :
    remainder4Coefficient4.coeff 33 =
      (-268910057122057305478250620090368706296404789129515628047162552163536 : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_34 :
    remainder4Coefficient4.coeff 34 =
      (3481198797781684209070956684317895949047772854944209220912459640612329 : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_35 :
    remainder4Coefficient4.coeff 35 =
      -((4 * 10 ^ 70 +
        2069816978636529880430425659826320304601335396317106026328309534193026) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_36 :
    remainder4Coefficient4.coeff 36 =
      ((47 * 10 ^ 70 +
        5536130370315163552446002986249228242808138662942641834887666547654304) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_37 :
    remainder4Coefficient4.coeff 37 =
      -((503 * 10 ^ 70 +
        6970915915898173269949493334079766361445291771051351145502574069211145) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_38 :
    remainder4Coefficient4.coeff 38 =
      ((5008 * 10 ^ 70 +
        2348421387596190178569233681934397183215388035789187533245771462352539) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_39 :
    remainder4Coefficient4.coeff 39 =
      -((46821 * 10 ^ 70 +
        2584523497335007892118489726882105576133270819749688213003003912056483) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_40 :
    remainder4Coefficient4.coeff 40 =
      ((412210 * 10 ^ 70 +
        3629419870780469374736944838899145583746380813717256349694644740010618) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_41 :
    remainder4Coefficient4.coeff 41 =
      -((3422547 * 10 ^ 70 +
        5555055146385175787376660432902320860046826454458801815006411542101577) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_42 :
    remainder4Coefficient4.coeff 42 =
      ((26837227 * 10 ^ 70 +
        1167758742429686980912016990705175949893958474499170804116771530635570) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_43 :
    remainder4Coefficient4.coeff 43 =
      -((199000342 * 10 ^ 70 +
        1107239130615134314538521896054539121648499404799450119805927590087804) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_44 :
    remainder4Coefficient4.coeff 44 =
      ((1397134386 * 10 ^ 70 +
        8839114119078308667636063634342480538807532753824602470515720842262314) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_45 :
    remainder4Coefficient4.coeff 45 =
      -((9298275190 * 10 ^ 70 +
        5602499132277471137544688363989743544134612336130865600148734706931650) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_46 :
    remainder4Coefficient4.coeff 46 =
      ((58726129299 * 10 ^ 70 +
        1394987425914761020935733723801606879887569186278747467651786943915114) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_47 :
    remainder4Coefficient4.coeff 47 =
      -((352358577014 * 10 ^ 70 +
        1247329120526219461357067305299134329561334952556181129397913795136213) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_48 :
    remainder4Coefficient4.coeff 48 =
      ((2010475502705 * 10 ^ 70 +
        6326565649084614686255826952163620860493547554005842552351912479797296) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_49 :
    remainder4Coefficient4.coeff 49 =
      -((10919098153848 * 10 ^ 70 +
        3088849006561933257781743687354273382887569192273107570735936318719108) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_50 :
    remainder4Coefficient4.coeff 50 =
      ((56499059595260 * 10 ^ 70 +
        0312472701746886715272396274414098116356132902531490282719742507162890) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_51 :
    remainder4Coefficient4.coeff 51 =
      -((278762623395781 * 10 ^ 70 +
        1125038440162610369815678780453126310544486688132175893404019857607163) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_52 :
    remainder4Coefficient4.coeff 52 =
      ((1312563151471495 * 10 ^ 70 +
        4709493237340617472289138587068063357178774075995854126095530823876944) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_53 :
    remainder4Coefficient4.coeff 53 =
      -((5902469173874552 * 10 ^ 70 +
        3730060243736670659024274806605956595630888317433610193208711919217756) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_54 :
    remainder4Coefficient4.coeff 54 =
      ((25368429550744922 * 10 ^ 70 +
        2962422593388561023338289253930948841536496796464962494164370673492379) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_55 :
    remainder4Coefficient4.coeff 55 =
      -((104280252790568816 * 10 ^ 70 +
        3659089962353617150948759230586230270578392890381004328775234865826359) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_56 :
    remainder4Coefficient4.coeff 56 =
      ((410247670716327812 * 10 ^ 70 +
        3226978922889689751135255189417253951304064421564428774643224685708198) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_57 :
    remainder4Coefficient4.coeff 57 =
      -((1545603185594230299 * 10 ^ 70 +
        7777425665469858131214901928667178565055273229443110579427226750399534) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_58 :
    remainder4Coefficient4.coeff 58 =
      ((5579766659762988852 * 10 ^ 70 +
        5787495498228005445559530777811029662766103844299341402120193682014928) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_59 :
    remainder4Coefficient4.coeff 59 =
      -((19312799571455915326 * 10 ^ 70 +
        1095428853027805894466671764872070568018416002980709564247880332800749) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_60 :
    remainder4Coefficient4.coeff 60 =
      ((64123598648046353957 * 10 ^ 70 +
        7566359916704976215263096295825163666350783796849645613928417290951667) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_61 :
    remainder4Coefficient4.coeff 61 =
      -((204340352448663420486 * 10 ^ 70 +
        9060419829768585239228056752117392860892913253723345712130726749091264) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_62 :
    remainder4Coefficient4.coeff 62 =
      ((625262653027928975232 * 10 ^ 70 +
        9586258464150814772698687533048191760731560429491669466687835985439656) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_63 :
    remainder4Coefficient4.coeff 63 =
      -((1837977925247326697725 * 10 ^ 70 +
        6378624767047399592218473981087341215139760649451028790387149647667046) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_64 :
    remainder4Coefficient4.coeff 64 =
      ((5192472387558946323185 * 10 ^ 70 +
        5484436147838198290473502338160926051848179076417134326405674943731919) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_65 :
    remainder4Coefficient4.coeff 65 =
      -((14103944046598663618951 * 10 ^ 70 +
        9917730513354002508552127528782873838613482135539718630971389013991269) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_66 :
    remainder4Coefficient4.coeff 66 =
      ((36847321266820794210476 * 10 ^ 70 +
        9230249844726472640311402363998608128506467693836164857220459949323907) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_67 :
    remainder4Coefficient4.coeff 67 =
      -((92624781888426856985814 * 10 ^ 70 +
        9893143880278236732011122471547671096826986561165764563795194444860851) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_68 :
    remainder4Coefficient4.coeff 68 =
      ((224105337115893695498012 * 10 ^ 70 +
        7143120318489014495622948269508240459934559670554185019172046759429088) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_69 :
    remainder4Coefficient4.coeff 69 =
      -((522059322098771308955969 * 10 ^ 70 +
        7801768007439033769966637723136736146770053442272402277630651519310698) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_70 :
    remainder4Coefficient4.coeff 70 =
      ((1171279470717965460664504 * 10 ^ 70 +
        0267015796420237791812663679799033587508382564218194404891740601452651) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_71 :
    remainder4Coefficient4.coeff 71 =
      -((2531607099224979223840810 * 10 ^ 70 +
        8029045983027480503737953087159739436778866876725554564860683183055928) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_72 :
    remainder4Coefficient4.coeff 72 =
      ((5272799021302746891817609 * 10 ^ 70 +
        5632624327288438787582079842192948990184434419265842411403608671843023) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_73 :
    remainder4Coefficient4.coeff 73 =
      -((10585259667018243301605326 * 10 ^ 70 +
        7359017397246505655118297497023876002011665835779618948011892352387125) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_74 :
    remainder4Coefficient4.coeff 74 =
      ((20486882055607355997675195 * 10 ^ 70 +
        9701828573769151958448956131227286748294613918110651312348269341008785) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_75 :
    remainder4Coefficient4.coeff 75 =
      -((38234513163566550179918934 * 10 ^ 70 +
        9025950628455738998153058628668889069057607486296695895832740908053035) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_76 :
    remainder4Coefficient4.coeff 76 =
      ((68821592199388266185196598 * 10 ^ 70 +
        5123981910678457676707561291517953866616426430942848000707797088761643) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_77 :
    remainder4Coefficient4.coeff 77 =
      -((119497938719427052145339967 * 10 ^ 70 +
        4669143043602120433076946477214705233405569342296659478708314682688878) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_78 :
    remainder4Coefficient4.coeff 78 =
      ((200185629245334498267012310 * 10 ^ 70 +
        3833768920471961844183171669125055162880931413089027162548905515384973) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_79 :
    remainder4Coefficient4.coeff 79 =
      -((323597900651783888512377146 * 10 ^ 70 +
        8395913972185322271704500364188194359393680985910201638655046968318410) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_80 :
    remainder4Coefficient4.coeff 80 =
      ((504819078964217346364173275 * 10 ^ 70 +
        9064130092406132445737175093074842067579619038044864533626593236554200) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_81 :
    remainder4Coefficient4.coeff 81 =
      -((760104996931713523061946357 * 10 ^ 70 +
        5969210529300953962792129617132662136262721002621981321878704231469229) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_82 :
    remainder4Coefficient4.coeff 82 =
      ((1104748260958109602736940995 * 10 ^ 70 +
        8680996677193045406160091908871631726687233251891689132614334991561734) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_83 :
    remainder4Coefficient4.coeff 83 =
      -((1550039894944171929426261531 * 10 ^ 70 +
        6922173335598232377465026718183709162075842253383821768399749009009028) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_84 :
    remainder4Coefficient4.coeff 84 =
      ((2099635817601882465375984245 * 10 ^ 70 +
        5316433486781299060471962915079466864800455381412556420691958695643974) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_85 :
    remainder4Coefficient4.coeff 85 =
      -((2745947733558828359543759758 * 10 ^ 70 +
        7062504235179655080848080626927271249782722825257201026517768606743628) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_86 :
    remainder4Coefficient4.coeff 86 =
      ((3467427494206627981915665376 * 10 ^ 70 +
        4544177015132306643490744959233081469936091890337657894520392761516530) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_87 :
    remainder4Coefficient4.coeff 87 =
      -((4227688755108568721315539096 * 10 ^ 70 +
        0976769010667191094651315444291129518532673081146259616139665313163006) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_88 :
    remainder4Coefficient4.coeff 88 =
      ((4977220428643708569238497389 * 10 ^ 70 +
        9974932646606808412843799254079918694385412678777989546279227028588664) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_89 :
    remainder4Coefficient4.coeff 89 =
      -((5657972995158680361051411580 * 10 ^ 70 +
        1644863562327990884794512726787286056575044192210484323842853898965418) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
