/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData2
import Mathlib.Tactic.NormNum

/-!
# Recurrence 2 lookup certificate: A6 source coefficients, low half

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence2A6_coeff_0 :
    remainder2Coefficient6.coeff 0 =
      (-606 : ℚ) := by
  unfold
    remainder2Coefficient6
    remainder2Coefficient6Block0
    remainder2Coefficient6Chunk11
    remainder2Coefficient6Chunk10
    remainder2Coefficient6Chunk9
    remainder2Coefficient6Chunk8
    remainder2Coefficient6Chunk7
    remainder2Coefficient6Chunk6
    remainder2Coefficient6Chunk5
    remainder2Coefficient6Chunk4
    remainder2Coefficient6Chunk3
    remainder2Coefficient6Chunk2
    remainder2Coefficient6Chunk1
    remainder2Coefficient6Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A6_coeff_1 :
    remainder2Coefficient6.coeff 1 =
      (-264384 : ℚ) := by
  unfold
    remainder2Coefficient6
    remainder2Coefficient6Block0
    remainder2Coefficient6Chunk11
    remainder2Coefficient6Chunk10
    remainder2Coefficient6Chunk9
    remainder2Coefficient6Chunk8
    remainder2Coefficient6Chunk7
    remainder2Coefficient6Chunk6
    remainder2Coefficient6Chunk5
    remainder2Coefficient6Chunk4
    remainder2Coefficient6Chunk3
    remainder2Coefficient6Chunk2
    remainder2Coefficient6Chunk1
    remainder2Coefficient6Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A6_coeff_2 :
    remainder2Coefficient6.coeff 2 =
      (656868640 : ℚ) := by
  unfold
    remainder2Coefficient6
    remainder2Coefficient6Block0
    remainder2Coefficient6Chunk11
    remainder2Coefficient6Chunk10
    remainder2Coefficient6Chunk9
    remainder2Coefficient6Chunk8
    remainder2Coefficient6Chunk7
    remainder2Coefficient6Chunk6
    remainder2Coefficient6Chunk5
    remainder2Coefficient6Chunk4
    remainder2Coefficient6Chunk3
    remainder2Coefficient6Chunk2
    remainder2Coefficient6Chunk1
    remainder2Coefficient6Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A6_coeff_3 :
    remainder2Coefficient6.coeff 3 =
      (-43610885488 : ℚ) := by
  unfold
    remainder2Coefficient6
    remainder2Coefficient6Block0
    remainder2Coefficient6Chunk11
    remainder2Coefficient6Chunk10
    remainder2Coefficient6Chunk9
    remainder2Coefficient6Chunk8
    remainder2Coefficient6Chunk7
    remainder2Coefficient6Chunk6
    remainder2Coefficient6Chunk5
    remainder2Coefficient6Chunk4
    remainder2Coefficient6Chunk3
    remainder2Coefficient6Chunk2
    remainder2Coefficient6Chunk1
    remainder2Coefficient6Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A6_coeff_4 :
    remainder2Coefficient6.coeff 4 =
      (-7907413645917 : ℚ) := by
  unfold
    remainder2Coefficient6
    remainder2Coefficient6Block0
    remainder2Coefficient6Chunk11
    remainder2Coefficient6Chunk10
    remainder2Coefficient6Chunk9
    remainder2Coefficient6Chunk8
    remainder2Coefficient6Chunk7
    remainder2Coefficient6Chunk6
    remainder2Coefficient6Chunk5
    remainder2Coefficient6Chunk4
    remainder2Coefficient6Chunk3
    remainder2Coefficient6Chunk2
    remainder2Coefficient6Chunk1
    remainder2Coefficient6Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A6_coeff_5 :
    remainder2Coefficient6.coeff 5 =
      (237849108519302 : ℚ) := by
  unfold
    remainder2Coefficient6
    remainder2Coefficient6Block0
    remainder2Coefficient6Chunk11
    remainder2Coefficient6Chunk10
    remainder2Coefficient6Chunk9
    remainder2Coefficient6Chunk8
    remainder2Coefficient6Chunk7
    remainder2Coefficient6Chunk6
    remainder2Coefficient6Chunk5
    remainder2Coefficient6Chunk4
    remainder2Coefficient6Chunk3
    remainder2Coefficient6Chunk2
    remainder2Coefficient6Chunk1
    remainder2Coefficient6Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A6_coeff_6 :
    remainder2Coefficient6.coeff 6 =
      (17822290888370542 : ℚ) := by
  unfold
    remainder2Coefficient6
    remainder2Coefficient6Block0
    remainder2Coefficient6Chunk11
    remainder2Coefficient6Chunk10
    remainder2Coefficient6Chunk9
    remainder2Coefficient6Chunk8
    remainder2Coefficient6Chunk7
    remainder2Coefficient6Chunk6
    remainder2Coefficient6Chunk5
    remainder2Coefficient6Chunk4
    remainder2Coefficient6Chunk3
    remainder2Coefficient6Chunk2
    remainder2Coefficient6Chunk1
    remainder2Coefficient6Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A6_coeff_7 :
    remainder2Coefficient6.coeff 7 =
      (-60757622243990768 : ℚ) := by
  unfold
    remainder2Coefficient6
    remainder2Coefficient6Block0
    remainder2Coefficient6Chunk11
    remainder2Coefficient6Chunk10
    remainder2Coefficient6Chunk9
    remainder2Coefficient6Chunk8
    remainder2Coefficient6Chunk7
    remainder2Coefficient6Chunk6
    remainder2Coefficient6Chunk5
    remainder2Coefficient6Chunk4
    remainder2Coefficient6Chunk3
    remainder2Coefficient6Chunk2
    remainder2Coefficient6Chunk1
    remainder2Coefficient6Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A6_coeff_8 :
    remainder2Coefficient6.coeff 8 =
      (-15092317899760440692 : ℚ) := by
  unfold
    remainder2Coefficient6
    remainder2Coefficient6Block0
    remainder2Coefficient6Chunk11
    remainder2Coefficient6Chunk10
    remainder2Coefficient6Chunk9
    remainder2Coefficient6Chunk8
    remainder2Coefficient6Chunk7
    remainder2Coefficient6Chunk6
    remainder2Coefficient6Chunk5
    remainder2Coefficient6Chunk4
    remainder2Coefficient6Chunk3
    remainder2Coefficient6Chunk2
    remainder2Coefficient6Chunk1
    remainder2Coefficient6Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A6_coeff_9 :
    remainder2Coefficient6.coeff 9 =
      (-122739733042983787952 : ℚ) := by
  unfold
    remainder2Coefficient6
    remainder2Coefficient6Block0
    remainder2Coefficient6Chunk11
    remainder2Coefficient6Chunk10
    remainder2Coefficient6Chunk9
    remainder2Coefficient6Chunk8
    remainder2Coefficient6Chunk7
    remainder2Coefficient6Chunk6
    remainder2Coefficient6Chunk5
    remainder2Coefficient6Chunk4
    remainder2Coefficient6Chunk3
    remainder2Coefficient6Chunk2
    remainder2Coefficient6Chunk1
    remainder2Coefficient6Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A6_coeff_10 :
    remainder2Coefficient6.coeff 10 =
      (3980510503323414556252 : ℚ) := by
  unfold
    remainder2Coefficient6
    remainder2Coefficient6Block0
    remainder2Coefficient6Chunk11
    remainder2Coefficient6Chunk10
    remainder2Coefficient6Chunk9
    remainder2Coefficient6Chunk8
    remainder2Coefficient6Chunk7
    remainder2Coefficient6Chunk6
    remainder2Coefficient6Chunk5
    remainder2Coefficient6Chunk4
    remainder2Coefficient6Chunk3
    remainder2Coefficient6Chunk2
    remainder2Coefficient6Chunk1
    remainder2Coefficient6Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A6_coeff_11 :
    remainder2Coefficient6.coeff 11 =
      (80975272851461060031324 : ℚ) := by
  unfold
    remainder2Coefficient6
    remainder2Coefficient6Block0
    remainder2Coefficient6Chunk11
    remainder2Coefficient6Chunk10
    remainder2Coefficient6Chunk9
    remainder2Coefficient6Chunk8
    remainder2Coefficient6Chunk7
    remainder2Coefficient6Chunk6
    remainder2Coefficient6Chunk5
    remainder2Coefficient6Chunk4
    remainder2Coefficient6Chunk3
    remainder2Coefficient6Chunk2
    remainder2Coefficient6Chunk1
    remainder2Coefficient6Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A6_coeff_12 :
    remainder2Coefficient6.coeff 12 =
      (-339731311869300366432704 : ℚ) := by
  unfold
    remainder2Coefficient6
    remainder2Coefficient6Block0
    remainder2Coefficient6Chunk11
    remainder2Coefficient6Chunk10
    remainder2Coefficient6Chunk9
    remainder2Coefficient6Chunk8
    remainder2Coefficient6Chunk7
    remainder2Coefficient6Chunk6
    remainder2Coefficient6Chunk5
    remainder2Coefficient6Chunk4
    remainder2Coefficient6Chunk3
    remainder2Coefficient6Chunk2
    remainder2Coefficient6Chunk1
    remainder2Coefficient6Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A6_coeff_13 :
    remainder2Coefficient6.coeff 13 =
      (-14893034520022581397395970 : ℚ) := by
  unfold
    remainder2Coefficient6
    remainder2Coefficient6Block0
    remainder2Coefficient6Chunk11
    remainder2Coefficient6Chunk10
    remainder2Coefficient6Chunk9
    remainder2Coefficient6Chunk8
    remainder2Coefficient6Chunk7
    remainder2Coefficient6Chunk6
    remainder2Coefficient6Chunk5
    remainder2Coefficient6Chunk4
    remainder2Coefficient6Chunk3
    remainder2Coefficient6Chunk2
    remainder2Coefficient6Chunk1
    remainder2Coefficient6Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A6_coeff_14 :
    remainder2Coefficient6.coeff 14 =
      (-61507058526884679075023217 : ℚ) := by
  unfold
    remainder2Coefficient6
    remainder2Coefficient6Block0
    remainder2Coefficient6Chunk11
    remainder2Coefficient6Chunk10
    remainder2Coefficient6Chunk9
    remainder2Coefficient6Chunk8
    remainder2Coefficient6Chunk7
    remainder2Coefficient6Chunk6
    remainder2Coefficient6Chunk5
    remainder2Coefficient6Chunk4
    remainder2Coefficient6Chunk3
    remainder2Coefficient6Chunk2
    remainder2Coefficient6Chunk1
    remainder2Coefficient6Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A6_coeff_15 :
    remainder2Coefficient6.coeff 15 =
      (1557412099701861736209197599 : ℚ) := by
  unfold
    remainder2Coefficient6
    remainder2Coefficient6Block0
    remainder2Coefficient6Chunk11
    remainder2Coefficient6Chunk10
    remainder2Coefficient6Chunk9
    remainder2Coefficient6Chunk8
    remainder2Coefficient6Chunk7
    remainder2Coefficient6Chunk6
    remainder2Coefficient6Chunk5
    remainder2Coefficient6Chunk4
    remainder2Coefficient6Chunk3
    remainder2Coefficient6Chunk2
    remainder2Coefficient6Chunk1
    remainder2Coefficient6Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A6_coeff_16 :
    remainder2Coefficient6.coeff 16 =
      (11931824111968927302483079140 : ℚ) := by
  unfold
    remainder2Coefficient6
    remainder2Coefficient6Block0
    remainder2Coefficient6Chunk11
    remainder2Coefficient6Chunk10
    remainder2Coefficient6Chunk9
    remainder2Coefficient6Chunk8
    remainder2Coefficient6Chunk7
    remainder2Coefficient6Chunk6
    remainder2Coefficient6Chunk5
    remainder2Coefficient6Chunk4
    remainder2Coefficient6Chunk3
    remainder2Coefficient6Chunk2
    remainder2Coefficient6Chunk1
    remainder2Coefficient6Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A6_coeff_17 :
    remainder2Coefficient6.coeff 17 =
      (-74615194376512967677074331502 : ℚ) := by
  unfold
    remainder2Coefficient6
    remainder2Coefficient6Block0
    remainder2Coefficient6Chunk11
    remainder2Coefficient6Chunk10
    remainder2Coefficient6Chunk9
    remainder2Coefficient6Chunk8
    remainder2Coefficient6Chunk7
    remainder2Coefficient6Chunk6
    remainder2Coefficient6Chunk5
    remainder2Coefficient6Chunk4
    remainder2Coefficient6Chunk3
    remainder2Coefficient6Chunk2
    remainder2Coefficient6Chunk1
    remainder2Coefficient6Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A6_coeff_18 :
    remainder2Coefficient6.coeff 18 =
      (-1147978231603713844269051911554 : ℚ) := by
  unfold
    remainder2Coefficient6
    remainder2Coefficient6Block0
    remainder2Coefficient6Chunk11
    remainder2Coefficient6Chunk10
    remainder2Coefficient6Chunk9
    remainder2Coefficient6Chunk8
    remainder2Coefficient6Chunk7
    remainder2Coefficient6Chunk6
    remainder2Coefficient6Chunk5
    remainder2Coefficient6Chunk4
    remainder2Coefficient6Chunk3
    remainder2Coefficient6Chunk2
    remainder2Coefficient6Chunk1
    remainder2Coefficient6Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A6_coeff_19 :
    remainder2Coefficient6.coeff 19 =
      (1703605390132880923263815628087 : ℚ) := by
  unfold
    remainder2Coefficient6
    remainder2Coefficient6Block0
    remainder2Coefficient6Chunk11
    remainder2Coefficient6Chunk10
    remainder2Coefficient6Chunk9
    remainder2Coefficient6Chunk8
    remainder2Coefficient6Chunk7
    remainder2Coefficient6Chunk6
    remainder2Coefficient6Chunk5
    remainder2Coefficient6Chunk4
    remainder2Coefficient6Chunk3
    remainder2Coefficient6Chunk2
    remainder2Coefficient6Chunk1
    remainder2Coefficient6Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A6_coeff_20 :
    remainder2Coefficient6.coeff 20 =
      (65342815875548638995525416873715 : ℚ) := by
  unfold
    remainder2Coefficient6
    remainder2Coefficient6Block0
    remainder2Coefficient6Chunk11
    remainder2Coefficient6Chunk10
    remainder2Coefficient6Chunk9
    remainder2Coefficient6Chunk8
    remainder2Coefficient6Chunk7
    remainder2Coefficient6Chunk6
    remainder2Coefficient6Chunk5
    remainder2Coefficient6Chunk4
    remainder2Coefficient6Chunk3
    remainder2Coefficient6Chunk2
    remainder2Coefficient6Chunk1
    remainder2Coefficient6Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A6_coeff_21 :
    remainder2Coefficient6.coeff 21 =
      (46764779696712004097218540893258 : ℚ) := by
  unfold
    remainder2Coefficient6
    remainder2Coefficient6Block0
    remainder2Coefficient6Chunk11
    remainder2Coefficient6Chunk10
    remainder2Coefficient6Chunk9
    remainder2Coefficient6Chunk8
    remainder2Coefficient6Chunk7
    remainder2Coefficient6Chunk6
    remainder2Coefficient6Chunk5
    remainder2Coefficient6Chunk4
    remainder2Coefficient6Chunk3
    remainder2Coefficient6Chunk2
    remainder2Coefficient6Chunk1
    remainder2Coefficient6Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A6_coeff_22 :
    remainder2Coefficient6.coeff 22 =
      (-2756851892830333293894575180613507 : ℚ) := by
  unfold
    remainder2Coefficient6
    remainder2Coefficient6Block0
    remainder2Coefficient6Chunk11
    remainder2Coefficient6Chunk10
    remainder2Coefficient6Chunk9
    remainder2Coefficient6Chunk8
    remainder2Coefficient6Chunk7
    remainder2Coefficient6Chunk6
    remainder2Coefficient6Chunk5
    remainder2Coefficient6Chunk4
    remainder2Coefficient6Chunk3
    remainder2Coefficient6Chunk2
    remainder2Coefficient6Chunk1
    remainder2Coefficient6Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A6_coeff_23 :
    remainder2Coefficient6.coeff 23 =
      (-4973479925282740496115957637429406 : ℚ) := by
  unfold
    remainder2Coefficient6
    remainder2Coefficient6Block0
    remainder2Coefficient6Chunk11
    remainder2Coefficient6Chunk10
    remainder2Coefficient6Chunk9
    remainder2Coefficient6Chunk8
    remainder2Coefficient6Chunk7
    remainder2Coefficient6Chunk6
    remainder2Coefficient6Chunk5
    remainder2Coefficient6Chunk4
    remainder2Coefficient6Chunk3
    remainder2Coefficient6Chunk2
    remainder2Coefficient6Chunk1
    remainder2Coefficient6Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A6_coeff_24 :
    remainder2Coefficient6.coeff 24 =
      (90957482947576568207820968873219052 : ℚ) := by
  unfold
    remainder2Coefficient6
    remainder2Coefficient6Block0
    remainder2Coefficient6Chunk11
    remainder2Coefficient6Chunk10
    remainder2Coefficient6Chunk9
    remainder2Coefficient6Chunk8
    remainder2Coefficient6Chunk7
    remainder2Coefficient6Chunk6
    remainder2Coefficient6Chunk5
    remainder2Coefficient6Chunk4
    remainder2Coefficient6Chunk3
    remainder2Coefficient6Chunk2
    remainder2Coefficient6Chunk1
    remainder2Coefficient6Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A6_coeff_25 :
    remainder2Coefficient6.coeff 25 =
      (210316203154359032521086649236863646 : ℚ) := by
  unfold
    remainder2Coefficient6
    remainder2Coefficient6Block0
    remainder2Coefficient6Chunk11
    remainder2Coefficient6Chunk10
    remainder2Coefficient6Chunk9
    remainder2Coefficient6Chunk8
    remainder2Coefficient6Chunk7
    remainder2Coefficient6Chunk6
    remainder2Coefficient6Chunk5
    remainder2Coefficient6Chunk4
    remainder2Coefficient6Chunk3
    remainder2Coefficient6Chunk2
    remainder2Coefficient6Chunk1
    remainder2Coefficient6Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A6_coeff_26 :
    remainder2Coefficient6.coeff 26 =
      (-2519572862830697884162971473184893653 : ℚ) := by
  unfold
    remainder2Coefficient6
    remainder2Coefficient6Block0
    remainder2Coefficient6Chunk11
    remainder2Coefficient6Chunk10
    remainder2Coefficient6Chunk9
    remainder2Coefficient6Chunk8
    remainder2Coefficient6Chunk7
    remainder2Coefficient6Chunk6
    remainder2Coefficient6Chunk5
    remainder2Coefficient6Chunk4
    remainder2Coefficient6Chunk3
    remainder2Coefficient6Chunk2
    remainder2Coefficient6Chunk1
    remainder2Coefficient6Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A6_coeff_27 :
    remainder2Coefficient6.coeff 27 =
      (-5716537617376765869030209898778114261 : ℚ) := by
  unfold
    remainder2Coefficient6
    remainder2Coefficient6Block0
    remainder2Coefficient6Chunk11
    remainder2Coefficient6Chunk10
    remainder2Coefficient6Chunk9
    remainder2Coefficient6Chunk8
    remainder2Coefficient6Chunk7
    remainder2Coefficient6Chunk6
    remainder2Coefficient6Chunk5
    remainder2Coefficient6Chunk4
    remainder2Coefficient6Chunk3
    remainder2Coefficient6Chunk2
    remainder2Coefficient6Chunk1
    remainder2Coefficient6Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A6_coeff_28 :
    remainder2Coefficient6.coeff 28 =
      (60367025213541084292114337935339630656 : ℚ) := by
  unfold
    remainder2Coefficient6
    remainder2Coefficient6Block0
    remainder2Coefficient6Chunk11
    remainder2Coefficient6Chunk10
    remainder2Coefficient6Chunk9
    remainder2Coefficient6Chunk8
    remainder2Coefficient6Chunk7
    remainder2Coefficient6Chunk6
    remainder2Coefficient6Chunk5
    remainder2Coefficient6Chunk4
    remainder2Coefficient6Chunk3
    remainder2Coefficient6Chunk2
    remainder2Coefficient6Chunk1
    remainder2Coefficient6Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A6_coeff_29 :
    remainder2Coefficient6.coeff 29 =
      (106109478758528122081569249927892450975 : ℚ) := by
  unfold
    remainder2Coefficient6
    remainder2Coefficient6Block0
    remainder2Coefficient6Chunk11
    remainder2Coefficient6Chunk10
    remainder2Coefficient6Chunk9
    remainder2Coefficient6Chunk8
    remainder2Coefficient6Chunk7
    remainder2Coefficient6Chunk6
    remainder2Coefficient6Chunk5
    remainder2Coefficient6Chunk4
    remainder2Coefficient6Chunk3
    remainder2Coefficient6Chunk2
    remainder2Coefficient6Chunk1
    remainder2Coefficient6Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A6_coeff_30 :
    remainder2Coefficient6.coeff 30 =
      (-1258161069668623656362952421948325399372 : ℚ) := by
  unfold
    remainder2Coefficient6
    remainder2Coefficient6Block0
    remainder2Coefficient6Chunk11
    remainder2Coefficient6Chunk10
    remainder2Coefficient6Chunk9
    remainder2Coefficient6Chunk8
    remainder2Coefficient6Chunk7
    remainder2Coefficient6Chunk6
    remainder2Coefficient6Chunk5
    remainder2Coefficient6Chunk4
    remainder2Coefficient6Chunk3
    remainder2Coefficient6Chunk2
    remainder2Coefficient6Chunk1
    remainder2Coefficient6Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A6_coeff_31 :
    remainder2Coefficient6.coeff 31 =
      (-1140152263465682044046210616394825658004 : ℚ) := by
  unfold
    remainder2Coefficient6
    remainder2Coefficient6Block0
    remainder2Coefficient6Chunk11
    remainder2Coefficient6Chunk10
    remainder2Coefficient6Chunk9
    remainder2Coefficient6Chunk8
    remainder2Coefficient6Chunk7
    remainder2Coefficient6Chunk6
    remainder2Coefficient6Chunk5
    remainder2Coefficient6Chunk4
    remainder2Coefficient6Chunk3
    remainder2Coefficient6Chunk2
    remainder2Coefficient6Chunk1
    remainder2Coefficient6Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A6_coeff_32 :
    remainder2Coefficient6.coeff 32 =
      (22303221764783494685504179773267006285479 : ℚ) := by
  unfold
    remainder2Coefficient6
    remainder2Coefficient6Block0
    remainder2Coefficient6Chunk11
    remainder2Coefficient6Chunk10
    remainder2Coefficient6Chunk9
    remainder2Coefficient6Chunk8
    remainder2Coefficient6Chunk7
    remainder2Coefficient6Chunk6
    remainder2Coefficient6Chunk5
    remainder2Coefficient6Chunk4
    remainder2Coefficient6Chunk3
    remainder2Coefficient6Chunk2
    remainder2Coefficient6Chunk1
    remainder2Coefficient6Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A6_coeff_33 :
    remainder2Coefficient6.coeff 33 =
      (-3068732178837805852846609862113546712980 : ℚ) := by
  unfold
    remainder2Coefficient6
    remainder2Coefficient6Block0
    remainder2Coefficient6Chunk11
    remainder2Coefficient6Chunk10
    remainder2Coefficient6Chunk9
    remainder2Coefficient6Chunk8
    remainder2Coefficient6Chunk7
    remainder2Coefficient6Chunk6
    remainder2Coefficient6Chunk5
    remainder2Coefficient6Chunk4
    remainder2Coefficient6Chunk3
    remainder2Coefficient6Chunk2
    remainder2Coefficient6Chunk1
    remainder2Coefficient6Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A6_coeff_34 :
    remainder2Coefficient6.coeff 34 =
      (-321295042349681723632820191220560028096900 : ℚ) := by
  unfold
    remainder2Coefficient6
    remainder2Coefficient6Block0
    remainder2Coefficient6Chunk11
    remainder2Coefficient6Chunk10
    remainder2Coefficient6Chunk9
    remainder2Coefficient6Chunk8
    remainder2Coefficient6Chunk7
    remainder2Coefficient6Chunk6
    remainder2Coefficient6Chunk5
    remainder2Coefficient6Chunk4
    remainder2Coefficient6Chunk3
    remainder2Coefficient6Chunk2
    remainder2Coefficient6Chunk1
    remainder2Coefficient6Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A6_coeff_35 :
    remainder2Coefficient6.coeff 35 =
      (424684769546239265370557834075128561258657 : ℚ) := by
  unfold
    remainder2Coefficient6
    remainder2Coefficient6Block0
    remainder2Coefficient6Chunk11
    remainder2Coefficient6Chunk10
    remainder2Coefficient6Chunk9
    remainder2Coefficient6Chunk8
    remainder2Coefficient6Chunk7
    remainder2Coefficient6Chunk6
    remainder2Coefficient6Chunk5
    remainder2Coefficient6Chunk4
    remainder2Coefficient6Chunk3
    remainder2Coefficient6Chunk2
    remainder2Coefficient6Chunk1
    remainder2Coefficient6Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A6_coeff_36 :
    remainder2Coefficient6.coeff 36 =
      (3467010735621713056201496621093019705005373 : ℚ) := by
  unfold
    remainder2Coefficient6
    remainder2Coefficient6Block0
    remainder2Coefficient6Chunk11
    remainder2Coefficient6Chunk10
    remainder2Coefficient6Chunk9
    remainder2Coefficient6Chunk8
    remainder2Coefficient6Chunk7
    remainder2Coefficient6Chunk6
    remainder2Coefficient6Chunk5
    remainder2Coefficient6Chunk4
    remainder2Coefficient6Chunk3
    remainder2Coefficient6Chunk2
    remainder2Coefficient6Chunk1
    remainder2Coefficient6Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A6_coeff_37 :
    remainder2Coefficient6.coeff 37 =
      (-9820907169482207987595217407352126266374824 : ℚ) := by
  unfold
    remainder2Coefficient6
    remainder2Coefficient6Block0
    remainder2Coefficient6Chunk11
    remainder2Coefficient6Chunk10
    remainder2Coefficient6Chunk9
    remainder2Coefficient6Chunk8
    remainder2Coefficient6Chunk7
    remainder2Coefficient6Chunk6
    remainder2Coefficient6Chunk5
    remainder2Coefficient6Chunk4
    remainder2Coefficient6Chunk3
    remainder2Coefficient6Chunk2
    remainder2Coefficient6Chunk1
    remainder2Coefficient6Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A6_coeff_38 :
    remainder2Coefficient6.coeff 38 =
      (-22643107225379856272866206550665913259766049 : ℚ) := by
  unfold
    remainder2Coefficient6
    remainder2Coefficient6Block0
    remainder2Coefficient6Chunk11
    remainder2Coefficient6Chunk10
    remainder2Coefficient6Chunk9
    remainder2Coefficient6Chunk8
    remainder2Coefficient6Chunk7
    remainder2Coefficient6Chunk6
    remainder2Coefficient6Chunk5
    remainder2Coefficient6Chunk4
    remainder2Coefficient6Chunk3
    remainder2Coefficient6Chunk2
    remainder2Coefficient6Chunk1
    remainder2Coefficient6Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A6_coeff_39 :
    remainder2Coefficient6.coeff 39 =
      (134638847786245837888592364557673177253229780 : ℚ) := by
  unfold
    remainder2Coefficient6
    remainder2Coefficient6Block0
    remainder2Coefficient6Chunk11
    remainder2Coefficient6Chunk10
    remainder2Coefficient6Chunk9
    remainder2Coefficient6Chunk8
    remainder2Coefficient6Chunk7
    remainder2Coefficient6Chunk6
    remainder2Coefficient6Chunk5
    remainder2Coefficient6Chunk4
    remainder2Coefficient6Chunk3
    remainder2Coefficient6Chunk2
    remainder2Coefficient6Chunk1
    remainder2Coefficient6Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A6_coeff_40 :
    remainder2Coefficient6.coeff 40 =
      (-14699805210117737208311297643153352365036420 : ℚ) := by
  unfold
    remainder2Coefficient6
    remainder2Coefficient6Block0
    remainder2Coefficient6Chunk11
    remainder2Coefficient6Chunk10
    remainder2Coefficient6Chunk9
    remainder2Coefficient6Chunk8
    remainder2Coefficient6Chunk7
    remainder2Coefficient6Chunk6
    remainder2Coefficient6Chunk5
    remainder2Coefficient6Chunk4
    remainder2Coefficient6Chunk3
    remainder2Coefficient6Chunk2
    remainder2Coefficient6Chunk1
    remainder2Coefficient6Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A6_coeff_41 :
    remainder2Coefficient6.coeff 41 =
      (-1140838767007516959294651878397634074067432175 : ℚ) := by
  unfold
    remainder2Coefficient6
    remainder2Coefficient6Block0
    remainder2Coefficient6Chunk11
    remainder2Coefficient6Chunk10
    remainder2Coefficient6Chunk9
    remainder2Coefficient6Chunk8
    remainder2Coefficient6Chunk7
    remainder2Coefficient6Chunk6
    remainder2Coefficient6Chunk5
    remainder2Coefficient6Chunk4
    remainder2Coefficient6Chunk3
    remainder2Coefficient6Chunk2
    remainder2Coefficient6Chunk1
    remainder2Coefficient6Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A6_coeff_42 :
    remainder2Coefficient6.coeff 42 =
      (2198291250583775650210278270666734838628936545 : ℚ) := by
  unfold
    remainder2Coefficient6
    remainder2Coefficient6Block0
    remainder2Coefficient6Chunk11
    remainder2Coefficient6Chunk10
    remainder2Coefficient6Chunk9
    remainder2Coefficient6Chunk8
    remainder2Coefficient6Chunk7
    remainder2Coefficient6Chunk6
    remainder2Coefficient6Chunk5
    remainder2Coefficient6Chunk4
    remainder2Coefficient6Chunk3
    remainder2Coefficient6Chunk2
    remainder2Coefficient6Chunk1
    remainder2Coefficient6Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A6_coeff_43 :
    remainder2Coefficient6.coeff 43 =
      (4377108880256740642198220811140850983490192676 : ℚ) := by
  unfold
    remainder2Coefficient6
    remainder2Coefficient6Block0
    remainder2Coefficient6Chunk11
    remainder2Coefficient6Chunk10
    remainder2Coefficient6Chunk9
    remainder2Coefficient6Chunk8
    remainder2Coefficient6Chunk7
    remainder2Coefficient6Chunk6
    remainder2Coefficient6Chunk5
    remainder2Coefficient6Chunk4
    remainder2Coefficient6Chunk3
    remainder2Coefficient6Chunk2
    remainder2Coefficient6Chunk1
    remainder2Coefficient6Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A6_coeff_44 :
    remainder2Coefficient6.coeff 44 =
      (-23751755542444203265532361883311010910235695327 : ℚ) := by
  unfold
    remainder2Coefficient6
    remainder2Coefficient6Block0
    remainder2Coefficient6Chunk11
    remainder2Coefficient6Chunk10
    remainder2Coefficient6Chunk9
    remainder2Coefficient6Chunk8
    remainder2Coefficient6Chunk7
    remainder2Coefficient6Chunk6
    remainder2Coefficient6Chunk5
    remainder2Coefficient6Chunk4
    remainder2Coefficient6Chunk3
    remainder2Coefficient6Chunk2
    remainder2Coefficient6Chunk1
    remainder2Coefficient6Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A6_coeff_45 :
    remainder2Coefficient6.coeff 45 =
      (19324817302042652217758620587384065055762449306 : ℚ) := by
  unfold
    remainder2Coefficient6
    remainder2Coefficient6Block0
    remainder2Coefficient6Chunk11
    remainder2Coefficient6Chunk10
    remainder2Coefficient6Chunk9
    remainder2Coefficient6Chunk8
    remainder2Coefficient6Chunk7
    remainder2Coefficient6Chunk6
    remainder2Coefficient6Chunk5
    remainder2Coefficient6Chunk4
    remainder2Coefficient6Chunk3
    remainder2Coefficient6Chunk2
    remainder2Coefficient6Chunk1
    remainder2Coefficient6Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A6_coeff_46 :
    remainder2Coefficient6.coeff 46 =
      (101615939163603552285300697518056435893445132998 : ℚ) := by
  unfold
    remainder2Coefficient6
    remainder2Coefficient6Block0
    remainder2Coefficient6Chunk11
    remainder2Coefficient6Chunk10
    remainder2Coefficient6Chunk9
    remainder2Coefficient6Chunk8
    remainder2Coefficient6Chunk7
    remainder2Coefficient6Chunk6
    remainder2Coefficient6Chunk5
    remainder2Coefficient6Chunk4
    remainder2Coefficient6Chunk3
    remainder2Coefficient6Chunk2
    remainder2Coefficient6Chunk1
    remainder2Coefficient6Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A6_coeff_47 :
    remainder2Coefficient6.coeff 47 =
      (-317667961885729755212373371552547149669387921084 : ℚ) := by
  unfold
    remainder2Coefficient6
    remainder2Coefficient6Block0
    remainder2Coefficient6Chunk11
    remainder2Coefficient6Chunk10
    remainder2Coefficient6Chunk9
    remainder2Coefficient6Chunk8
    remainder2Coefficient6Chunk7
    remainder2Coefficient6Chunk6
    remainder2Coefficient6Chunk5
    remainder2Coefficient6Chunk4
    remainder2Coefficient6Chunk3
    remainder2Coefficient6Chunk2
    remainder2Coefficient6Chunk1
    remainder2Coefficient6Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
