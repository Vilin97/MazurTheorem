/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData2
import Mathlib.Tactic.NormNum

/-!
# Recurrence 2 lookup certificate: C1 source coefficients, low half

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence2C1_coeff_0 :
    remainder4Coefficient1.coeff 0 =
      (0 : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_1 :
    remainder4Coefficient1.coeff 1 =
      (-49864 : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_2 :
    remainder4Coefficient1.coeff 2 =
      (142028948 : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_3 :
    remainder4Coefficient1.coeff 3 =
      (344400204764 : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_4 :
    remainder4Coefficient1.coeff 4 =
      (-587903610648779 : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_5 :
    remainder4Coefficient1.coeff 5 =
      (158035318466840996 : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_6 :
    remainder4Coefficient1.coeff 6 =
      (5772722755895982907 : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_7 :
    remainder4Coefficient1.coeff 7 =
      (-3971490080024822192413 : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_8 :
    remainder4Coefficient1.coeff 8 =
      (292652123040945272506269 : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_9 :
    remainder4Coefficient1.coeff 9 =
      (-107118672277416844731585299 : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_10 :
    remainder4Coefficient1.coeff 10 =
      (49104202880088014971535860196 : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_11 :
    remainder4Coefficient1.coeff 11 =
      (-14214096746171581073373883013493 : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_12 :
    remainder4Coefficient1.coeff 12 =
      (3136116976645669102440238442528505 : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_13 :
    remainder4Coefficient1.coeff 13 =
      (-553175092455905043213051246143020842 : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_14 :
    remainder4Coefficient1.coeff 14 =
      (79750547286391391475211516919307864378 : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_15 :
    remainder4Coefficient1.coeff 15 =
      (-9569938800838338416909800255924360824985 : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_16 :
    remainder4Coefficient1.coeff 16 =
      (969754651769990576106064394879194168969595 : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_17 :
    remainder4Coefficient1.coeff 17 =
      (-83964776017962601868543027016355974948108380 : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_18 :
    remainder4Coefficient1.coeff 18 =
      (6273926971987303911366815435118483731917436353 : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_19 :
    remainder4Coefficient1.coeff 19 =
      (-408071179054335301489933550987499700628272411498 : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_20 :
    remainder4Coefficient1.coeff 20 =
      (23280093578653574715187356656115616759329464117735 : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_21 :
    remainder4Coefficient1.coeff 21 =
      (-1172803729453016030230311719931029727325551630500514 : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_22 :
    remainder4Coefficient1.coeff 22 =
      (52493206444990632314214067124443872028382507959715506 : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_23 :
    remainder4Coefficient1.coeff 23 =
      (-2099022067975498985007779493293867910670290608749656750 : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_24 :
    remainder4Coefficient1.coeff 24 =
      (75362672726742822801985248290865075485180660447016592265 : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_25 :
    remainder4Coefficient1.coeff 25 =
      (-2440782889814689114143345791756460874707886213473249228266 : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_26 :
    remainder4Coefficient1.coeff 26 =
      (71611976960909361709623286107178577864223922136607516429486 : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_27 :
    remainder4Coefficient1.coeff 27 =
      (-1910893655236790414036807360120439706498056222349982999372260 : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_28 :
    remainder4Coefficient1.coeff 28 =
      (46544511128236073210085191888112542851680838041596196178995233 : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_29 :
    remainder4Coefficient1.coeff 29 =
      (-1038382401547817885136538493771201872301813264476381906664283005 : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_30 :
    remainder4Coefficient1.coeff 30 =
      (21285255821139194749000870147779267836589650298476565440425515592 : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_31 :
    remainder4Coefficient1.coeff 31 =
      (-402085487617173171346990294959042376926569851681638036112426825704 : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_32 :
    remainder4Coefficient1.coeff 32 =
      (7019056457487341598636866118648688426911261501437102308811044247647 : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_33 :
    remainder4Coefficient1.coeff 33 =
      (-113523928149350087463274312433599322256128549853878190619109597165150 : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_34 :
    remainder4Coefficient1.coeff 34 =
      (1705308121530463853100420746914649885839122515704567802777551156880432 : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_35 :
    remainder4Coefficient1.coeff 35 =
      -((2 * 10 ^ 70 +
        3846242155032942185219835867887039027276005848195794060774553771719276) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_36 :
    remainder4Coefficient1.coeff 36 =
      ((31 * 10 ^ 70 +
        1081990263117924439353141722672607209777681404731533157872778141782439) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_37 :
    remainder4Coefficient1.coeff 37 =
      -((379 * 10 ^ 70 +
        3582370910840075862409938468717334008044243103250093032519498845893707) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_38 :
    remainder4Coefficient1.coeff 38 =
      ((4332 * 10 ^ 70 +
        8679102116464914644499967959765679694413608273947868630111004415558231) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_39 :
    remainder4Coefficient1.coeff 39 =
      -((46434 * 10 ^ 70 +
        1412824802207795165982896394565698905327169863766004237044652872787051) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_40 :
    remainder4Coefficient1.coeff 40 =
      ((467709 * 10 ^ 70 +
        9489640300693453277827296233261471078251682098182814108216217126233074) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_41 :
    remainder4Coefficient1.coeff 41 =
      -((4434999 * 10 ^ 70 +
        3169001452735916826949746261266378307625072208658338631430722105224758) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_42 :
    remainder4Coefficient1.coeff 42 =
      ((39650697 * 10 ^ 70 +
        4715509006355921014001756983287399272159843432897646526140258307256269) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_43 :
    remainder4Coefficient1.coeff 43 =
      -((334715223 * 10 ^ 70 +
        1218939706398567819690138921574942427585452799742893316378194253424408) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_44 :
    remainder4Coefficient1.coeff 44 =
      ((2671537060 * 10 ^ 70 +
        2051296174841611855241922811619513307918884962763545869732363137094506) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_45 :
    remainder4Coefficient1.coeff 45 =
      -((20186943079 * 10 ^ 70 +
        0592368397514798445235365221231949766144764030429083619970355494260923) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_46 :
    remainder4Coefficient1.coeff 46 =
      ((144589483213 * 10 ^ 70 +
        8634850830470801259681251655578745859131861940650802324456658941038276) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_47 :
    remainder4Coefficient1.coeff 47 =
      -((982800184742 * 10 ^ 70 +
        4781282784301230391310291474605166532410612621780784206841688976628421) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_48 :
    remainder4Coefficient1.coeff 48 =
      ((6346521276594 * 10 ^ 70 +
        5515894754749045243451932014894939781253382315596239544403847447594929) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_49 :
    remainder4Coefficient1.coeff 49 =
      -((38976547488308 * 10 ^ 70 +
        8535081623269732907378387651721548672443547865407337010760433724411380) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_50 :
    remainder4Coefficient1.coeff 50 =
      ((227876815132903 * 10 ^ 70 +
        8130399749565011639291539228787923292760631720261034048010849231666858) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_51 :
    remainder4Coefficient1.coeff 51 =
      -((1269510450582678 * 10 ^ 70 +
        2892481863198292581256383414011578747231470300667231198801565973426807) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_52 :
    remainder4Coefficient1.coeff 52 =
      ((6745301733634627 * 10 ^ 70 +
        2231776744779339964697030812369871132254799924513142076707324150166703) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_53 :
    remainder4Coefficient1.coeff 53 =
      -((34210980983408997 * 10 ^ 70 +
        8565791398551663863949000565087988472441523123412289097836462120581266) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_54 :
    remainder4Coefficient1.coeff 54 =
      ((165760221770890667 * 10 ^ 70 +
        8224452479287825958484598081492463395293895852036027373081113385729932) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_55 :
    remainder4Coefficient1.coeff 55 =
      -((767856092205903478 * 10 ^ 70 +
        7722332295922980439961774002758239776092657012760543654233121873190130) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_56 :
    remainder4Coefficient1.coeff 56 =
      ((3403153384502619035 * 10 ^ 70 +
        2943571461712980749550121587784121770683821147023182173060110273946781) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_57 :
    remainder4Coefficient1.coeff 57 =
      -((14440660066567410247 * 10 ^ 70 +
        0287980673722551576562591887761278526370852514753630119267755802479784) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_58 :
    remainder4Coefficient1.coeff 58 =
      ((58706074425889142959 * 10 ^ 70 +
        4557604513109674847348769489972300756774014339650318526386503308724496) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_59 :
    remainder4Coefficient1.coeff 59 =
      -((228792544603131752478 * 10 ^ 70 +
        5915767155317042018359168516557019633578765027858830736157915102047096) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_60 :
    remainder4Coefficient1.coeff 60 =
      ((855307495182810774917 * 10 ^ 70 +
        0313852133928521286735576802571062556827825680954988027449065505642184) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_61 :
    remainder4Coefficient1.coeff 61 =
      -((3068810333464351392916 * 10 ^ 70 +
        3822702293769927939608367962889539753670501169483301692722715689352725) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_62 :
    remainder4Coefficient1.coeff 62 =
      ((10573495422147437811870 * 10 ^ 70 +
        6975960113146400135892896094096316851286366501720999586773409669860056) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_63 :
    remainder4Coefficient1.coeff 63 =
      -((35001726155326599916621 * 10 ^ 70 +
        8973739555062517366541477481343072499966506009582570851383762977004599) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_64 :
    remainder4Coefficient1.coeff 64 =
      ((111376348915207219057481 * 10 ^ 70 +
        0730887326874863757760322028849217993721538823215105066748692981063704) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_65 :
    remainder4Coefficient1.coeff 65 =
      -((340822769397646769605329 * 10 ^ 70 +
        6729322117803950111470866598248880441804984284505792543178905136933392) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_66 :
    remainder4Coefficient1.coeff 66 =
      ((1003426254664093251011625 * 10 ^ 70 +
        7805689974797051060371536773000316963738713186463382329270374169266577) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_67 :
    remainder4Coefficient1.coeff 67 =
      -((2843431416857457669197928 * 10 ^ 70 +
        4540009642622081370233800703244254389781134029420728506196320001190545) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_68 :
    remainder4Coefficient1.coeff 68 =
      ((7758364460356831420654464 * 10 ^ 70 +
        6582705060785504859812589618160858740754180295319239420551237993013739) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_69 :
    remainder4Coefficient1.coeff 69 =
      -((20390518154643844804702799 * 10 ^ 70 +
        5988998241373603909354136066005146736381546554364670148342408963828596) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_70 :
    remainder4Coefficient1.coeff 70 =
      ((51637923203455014761685106 * 10 ^ 70 +
        9286848232462922558845912860433930888479075839968059105391075478587075) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_71 :
    remainder4Coefficient1.coeff 71 =
      -((126047720140464444919525213 * 10 ^ 70 +
        1338711699635030830934936403236827765612243610584452521167171063194312) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_72 :
    remainder4Coefficient1.coeff 72 =
      ((296662126045632265429404094 * 10 ^ 70 +
        9018023439517491037496040843323362386345956725018735847397895487915472) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_73 :
    remainder4Coefficient1.coeff 73 =
      -((673406662380562441615730444 * 10 ^ 70 +
        5650599672541830834807385947703248823246143331196618802803505502368546) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_74 :
    remainder4Coefficient1.coeff 74 =
      ((1474689695816068070169752835 * 10 ^ 70 +
        3137200631707956748052241466478415799451737103455948953483302972125776) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_75 :
    remainder4Coefficient1.coeff 75 =
      -((3116335736672213691230325280 * 10 ^ 70 +
        3538908418090275412786499396601039306993363165059220917471457421234405) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_76 :
    remainder4Coefficient1.coeff 76 =
      ((6356434037364467604513070668 * 10 ^ 70 +
        6824225731186468962565164485480569693331231251160254622666918536864800) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_77 :
    remainder4Coefficient1.coeff 77 =
      -((12517196451644997210490589661 * 10 ^ 70 +
        8952793572317513989497192809713253440284703671390066152637559923532985) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_78 :
    remainder4Coefficient1.coeff 78 =
      ((23802177535863872741551485090 * 10 ^ 70 +
        0292887210790698825334823730949289720404805058300699356312956639384317) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_79 :
    remainder4Coefficient1.coeff 79 =
      -((43714735914136138419305211733 * 10 ^ 70 +
        4788662897140316478402336430454409513983949137084300037063944551147298) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_80 :
    remainder4Coefficient1.coeff 80 =
      ((77556782190389065407585725964 * 10 ^ 70 +
        4929527469090857054185679096334035236775874461065468012444502764401853) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_81 :
    remainder4Coefficient1.coeff 81 =
      -((132943038148629912951468831578 * 10 ^ 70 +
        0152789368545902747493388273741052920547537094210665543074496889729088) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_82 :
    remainder4Coefficient1.coeff 82 =
      ((220207724890644743085359855389 * 10 ^ 70 +
        0114225462401913753593214322415907050455633764214377182684412614230752) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_83 :
    remainder4Coefficient1.coeff 83 =
      -((352518670128378308979139979447 * 10 ^ 70 +
        3234358749932651839835564180854538276137875438787011874149603030403537) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_84 :
    remainder4Coefficient1.coeff 84 =
      ((545469161476402307353104070230 * 10 ^ 70 +
        7656316847916493234860914112510162245447135758104736039368205730526987) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_85 :
    remainder4Coefficient1.coeff 85 =
      -((815919284864171231676430146758 * 10 ^ 70 +
        6974465266589872663432128449433840896684202728687529278870045599237988) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_86 :
    remainder4Coefficient1.coeff 86 =
      ((1179935232981088818057549535421 * 10 ^ 70 +
        8191550837717204166369509184452180437352878650046362069941822351364446) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_87 :
    remainder4Coefficient1.coeff 87 =
      -((1649844212643411643634331665034 * 10 ^ 70 +
        2857350982664367409294799767717257040382397524622402320096834649432197) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_88 :
    remainder4Coefficient1.coeff 88 =
      ((2230674435053702559040424812780 * 10 ^ 70 +
        7897881866369854183869091199971464307651807369111756289413874227776966) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_89 :
    remainder4Coefficient1.coeff 89 =
      -((2916537555750793141066193944546 * 10 ^ 70 +
        2312656643238168859178457645928940452388899103897512486821310163953291) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_90 :
    remainder4Coefficient1.coeff 90 =
      ((3687752601862470316747143276375 * 10 ^ 70 +
        5560008013785500787097519619926894089579994372133560093973497750182057) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_91 :
    remainder4Coefficient1.coeff 91 =
      -((4509606164795666378851292554584 * 10 ^ 70 +
        7092885709740495363050355230729174597368905770385258128005813899488456) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_92 :
    remainder4Coefficient1.coeff 92 =
      ((5333509602328363454579365935103 * 10 ^ 70 +
        5581515286902021828766395956721222300966167730267180761867430032672331) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_93 :
    remainder4Coefficient1.coeff 93 =
      -((6100921162395537341992001700498 * 10 ^ 70 +
        9634890789284671657517608093554963352535873853749814565156813007108409) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_94 :
    remainder4Coefficient1.coeff 94 =
      ((6749803593406874386655262991563 * 10 ^ 70 +
        9032723311724993287976959976215791065959150148108192669649856306506384) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_95 :
    remainder4Coefficient1.coeff 95 =
      -((7222725338548068760455368176789 * 10 ^ 70 +
        0608447778611744077227400614602145429245539912289115627539754637699390) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
