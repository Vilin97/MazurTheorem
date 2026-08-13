/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData2
import Mathlib.Tactic.NormNum

/-!
# Recurrence 2 lookup certificate: B3 source coefficients, low half

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence2B3_coeff_0 :
    remainder3Coefficient3.coeff 0 =
      (0 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_1 :
    remainder3Coefficient3.coeff 1 =
      (480 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_2 :
    remainder3Coefficient3.coeff 2 =
      (2101370 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_3 :
    remainder3Coefficient3.coeff 3 =
      (6741833232 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_4 :
    remainder3Coefficient3.coeff 4 =
      (1007725038232 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_5 :
    remainder3Coefficient3.coeff 5 =
      (1514210590514436 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_6 :
    remainder3Coefficient3.coeff 6 =
      (-252661954362651579 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_7 :
    remainder3Coefficient3.coeff 7 =
      (70580976386535404667 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_8 :
    remainder3Coefficient3.coeff 8 =
      (-7770078999813774941161 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_9 :
    remainder3Coefficient3.coeff 9 =
      (665619660847415358333691 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_10 :
    remainder3Coefficient3.coeff 10 =
      (-29151787061008139356079371 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_11 :
    remainder3Coefficient3.coeff 11 =
      (431573081168452503245082016 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_12 :
    remainder3Coefficient3.coeff 12 =
      (30765060231123124340888747962 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_13 :
    remainder3Coefficient3.coeff 13 =
      (-420465597786790140177689853690 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_14 :
    remainder3Coefficient3.coeff 14 =
      (-231635597859453393669645890767315 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_15 :
    remainder3Coefficient3.coeff 15 =
      (25672040339073566305162429711917504 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_16 :
    remainder3Coefficient3.coeff 16 =
      (-1592649904244241948776821944667945208 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_17 :
    remainder3Coefficient3.coeff 17 =
      (70157524981800905948027975244144740677 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_18 :
    remainder3Coefficient3.coeff 18 =
      (-2364120591100822355029001163835195851320 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_19 :
    remainder3Coefficient3.coeff 19 =
      (62761081465454613200917170451308753755965 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_20 :
    remainder3Coefficient3.coeff 20 =
      (-1318506620132714491021676215087936613503383 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_21 :
    remainder3Coefficient3.coeff 21 =
      (21363805450566397992596429376467518622113721 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_22 :
    remainder3Coefficient3.coeff 22 =
      (-239591519486512844355524506906757411025312820 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_23 :
    remainder3Coefficient3.coeff 23 =
      (838631976014592192045689475297883405338670433 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_24 :
    remainder3Coefficient3.coeff 24 =
      (39323680664207917462371268634588994878314588210 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_25 :
    remainder3Coefficient3.coeff 25 =
      (-1255110642812999386812854618143537947008519295245 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_26 :
    remainder3Coefficient3.coeff 26 =
      (24053754625448439086729037783714806004867064042388 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_27 :
    remainder3Coefficient3.coeff 27 =
      (-358260090509608225437473550360386781388050237382264 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_28 :
    remainder3Coefficient3.coeff 28 =
      (4458993574907075907833466976323982545417966441849142 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_29 :
    remainder3Coefficient3.coeff 29 =
      (-47902052794745215049494643059608532424443234199200138 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_30 :
    remainder3Coefficient3.coeff 30 =
      (452230724637998595531068226168393585178727164709934656 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_31 :
    remainder3Coefficient3.coeff 31 =
      (-3794690300542582961642781778549697535408669518720738785 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_32 :
    remainder3Coefficient3.coeff 32 =
      (28519195587756404058556484972768149611446839249356728281 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_33 :
    remainder3Coefficient3.coeff 33 =
      (-193006169853746414143059339818637808762978975764455612203 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_34 :
    remainder3Coefficient3.coeff 34 =
      (1180512781369252764224539615477987005850127381835100835434 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_35 :
    remainder3Coefficient3.coeff 35 =
      (-6540297908704906261785640102274014945053908943605902258910 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_36 :
    remainder3Coefficient3.coeff 36 =
      (32845376198865990567951542846521074366912829360068369899529 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_37 :
    remainder3Coefficient3.coeff 37 =
      (-149370660360551090862289677618089905267374498746780124414367 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_38 :
    remainder3Coefficient3.coeff 38 =
      (613047825618599045320058133249562112630192030938648579518817 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_39 :
    remainder3Coefficient3.coeff 39 =
      (-2254365055564034132731832311863235427197643124596087865032902 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_40 :
    remainder3Coefficient3.coeff 40 =
      (7321318705668383896097494672479343144359967198655430342717486 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_41 :
    remainder3Coefficient3.coeff 41 =
      (-20359196587192512199618778289586529741252603082861773640976589 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_42 :
    remainder3Coefficient3.coeff 42 =
      (44716004517758441781127530550017635633020047704487393900203363 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_43 :
    remainder3Coefficient3.coeff 43 =
      (-54547649269116285811940460593138403304655554475696782746415836 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_44 :
    remainder3Coefficient3.coeff 44 =
      (-125509718208091748382174758817225511947054422065220370360597262 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_45 :
    remainder3Coefficient3.coeff 45 =
      (1215361719188425093232555521244922693523846897761855976385158596 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_46 :
    remainder3Coefficient3.coeff 46 =
      (-5541279931949491542041626920062413590725488757902183037311898975 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_47 :
    remainder3Coefficient3.coeff 47 =
      (19436837625481187499608194721315137768824828232880362815327875540 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_48 :
    remainder3Coefficient3.coeff 48 =
      (-58004990475890653255376363542401572493144229521007025661597927553 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_49 :
    remainder3Coefficient3.coeff 49 =
      (153900138161638371624835943034609193562584588628438062946369208590 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_50 :
    remainder3Coefficient3.coeff 50 =
      (-369949353922945682441428217191353664500854628602529259821808490438 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_51 :
    remainder3Coefficient3.coeff 51 =
      (786531198946204696287853158862770410673610041919757365882480319893 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_52 :
    remainder3Coefficient3.coeff 52 =
      (-1315148907904428959344457482256885861297507477213747480995800745496 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_53 :
    remainder3Coefficient3.coeff 53 =
      (1119265223719573832872973365455181888551819724380791786529972617873 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_54 :
    remainder3Coefficient3.coeff 54 =
      (1103333684396259870377688427485826900794632598081214990524829572842 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_55 :
    remainder3Coefficient3.coeff 55 =
      (1879283894331569741651940079644695979141359000303877435700869098121 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_56 :
    remainder3Coefficient3.coeff 56 =
      (-55916938128361122720655140509859282882931568761100019509452561234930 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_57 :
    remainder3Coefficient3.coeff 57 =
      (237409309822331554824686877050604264611793171567334358766319913269188 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_58 :
    remainder3Coefficient3.coeff 58 =
      (-213809508961350916516566904523070525246423816908895380968995947186338 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_59 :
    remainder3Coefficient3.coeff 59 =
      (-2435613045093290359826760836596567532184760578143784772131849034201698 : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_60 :
    remainder3Coefficient3.coeff 60 =
      ((1 * 10 ^ 70 +
        3669025606547521390174941188337277461436254658068376501898396076304454) : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_61 :
    remainder3Coefficient3.coeff 61 =
      -((2 * 10 ^ 70 +
        9337314899757779683220696984335609046041918345516209208311730243348620) : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_62 :
    remainder3Coefficient3.coeff 62 =
      -((3 * 10 ^ 70 +
        6308947584604616756602443827076121828667671223942697206251844585543158) : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_63 :
    remainder3Coefficient3.coeff 63 =
      ((49 * 10 ^ 70 +
        7066274580660981369955743351611388439772409469801925676732534327609626) : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_64 :
    remainder3Coefficient3.coeff 64 =
      -((177 * 10 ^ 70 +
        0530895444771418085531175747306495574764841097798966157168987918658459) : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_65 :
    remainder3Coefficient3.coeff 65 =
      ((246 * 10 ^ 70 +
        7981732566273496085035602001082015752261480043597428754637415453115977) : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_66 :
    remainder3Coefficient3.coeff 66 =
      ((724 * 10 ^ 70 +
        1357216704572356197710263676729547799881075345243555549121601273000653) : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_67 :
    remainder3Coefficient3.coeff 67 =
      -((5601 * 10 ^ 70 +
        3296515130011635859672204617785145896963808738077525612998095820173738) : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_68 :
    remainder3Coefficient3.coeff 68 =
      ((17865 * 10 ^ 70 +
        7839627351753032682798882747466385046668110767113526829669925648872946) : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_69 :
    remainder3Coefficient3.coeff 69 =
      -((28299 * 10 ^ 70 +
        8781924408871682093359956131542837394822113871837939698690563478178401) : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_70 :
    remainder3Coefficient3.coeff 70 =
      -((29616 * 10 ^ 70 +
        7432209641770047161144972637366501188852007704895018441642063244091365) : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B3_coeff_71 :
    remainder3Coefficient3.coeff 71 =
      ((366354 * 10 ^ 70 +
        8145118652539719394997134023618733741136223405375632738092129050866093) : ℚ) := by
  unfold
    remainder3Coefficient3
    remainder3Coefficient3Block1
    remainder3Coefficient3Block0
    remainder3Coefficient3Chunk17
    remainder3Coefficient3Chunk16
    remainder3Coefficient3Chunk15
    remainder3Coefficient3Chunk14
    remainder3Coefficient3Chunk13
    remainder3Coefficient3Chunk12
    remainder3Coefficient3Chunk11
    remainder3Coefficient3Chunk10
    remainder3Coefficient3Chunk9
    remainder3Coefficient3Chunk8
    remainder3Coefficient3Chunk7
    remainder3Coefficient3Chunk6
    remainder3Coefficient3Chunk5
    remainder3Coefficient3Chunk4
    remainder3Coefficient3Chunk3
    remainder3Coefficient3Chunk2
    remainder3Coefficient3Chunk1
    remainder3Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
