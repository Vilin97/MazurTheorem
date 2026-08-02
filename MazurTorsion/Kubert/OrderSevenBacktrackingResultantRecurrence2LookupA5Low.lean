/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData2
import Mathlib.Tactic.NormNum

/-!
# Recurrence 2 lookup certificate: A5 source coefficients, low half

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence2A5_coeff_0 :
    remainder2Coefficient5.coeff 0 =
      (-8 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_1 :
    remainder2Coefficient5.coeff 1 =
      (-4584 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_2 :
    remainder2Coefficient5.coeff 2 =
      (58202904 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_3 :
    remainder2Coefficient5.coeff 3 =
      (-13173586573 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_4 :
    remainder2Coefficient5.coeff 4 =
      (-826150121927 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_5 :
    remainder2Coefficient5.coeff 5 =
      (152811697040613 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_6 :
    remainder2Coefficient5.coeff 6 =
      (1321979052167081 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_7 :
    remainder2Coefficient5.coeff 7 =
      (-239337682022022144 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_8 :
    remainder2Coefficient5.coeff 8 =
      (-4010384813694609235 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_9 :
    remainder2Coefficient5.coeff 9 =
      (140981990055572131702 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_10 :
    remainder2Coefficient5.coeff 10 =
      (2708132833691499223520 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_11 :
    remainder2Coefficient5.coeff 11 =
      (-11117019750973116692969 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_12 :
    remainder2Coefficient5.coeff 12 =
      (-1038032059894976781868696 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_13 :
    remainder2Coefficient5.coeff 13 =
      (-1516553408964565706773563 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_14 :
    remainder2Coefficient5.coeff 14 =
      (113435219738758599710588858 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_15 :
    remainder2Coefficient5.coeff 15 =
      (1281528474945542949359844633 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_16 :
    remainder2Coefficient5.coeff 16 =
      (-10949556985199660678063311825 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_17 :
    remainder2Coefficient5.coeff 17 =
      (-125392070547471792509348429414 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_18 :
    remainder2Coefficient5.coeff 18 =
      (215558598921243747288171008522 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_19 :
    remainder2Coefficient5.coeff 19 =
      (10589490421697306581022864221125 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_20 :
    remainder2Coefficient5.coeff 20 =
      (2185427701132490215696739421726 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_21 :
    remainder2Coefficient5.coeff 21 =
      (-509558385722369015881141643744004 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_22 :
    remainder2Coefficient5.coeff 22 =
      (-973972135415319263109760588480179 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_23 :
    remainder2Coefficient5.coeff 23 =
      (20888946531069052727010274247959325 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_24 :
    remainder2Coefficient5.coeff 24 =
      (48030170025326506913702104280824156 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_25 :
    remainder2Coefficient5.coeff 25 =
      (-676296360117176906042635167860569831 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_26 :
    remainder2Coefficient5.coeff 26 =
      (-1590442759177347388958151340464345290 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_27 :
    remainder2Coefficient5.coeff 27 =
      (19132701444277355709761164775195411393 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_28 :
    remainder2Coefficient5.coeff 28 =
      (34285205475050473373020125037058876286 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_29 :
    remainder2Coefficient5.coeff 29 =
      (-466785756737243618782844261631760400715 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_30 :
    remainder2Coefficient5.coeff 30 =
      (-412588225219251476476316758306081249061 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_31 :
    remainder2Coefficient5.coeff 31 =
      (9692705499083531167630753290409160783478 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_32 :
    remainder2Coefficient5.coeff 32 =
      (-2380408842837340426918169537663901078116 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_33 :
    remainder2Coefficient5.coeff 33 =
      (-163589430880070156827029618454308988307158 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_34 :
    remainder2Coefficient5.coeff 34 =
      (252102819302740101766946367034325092681392 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_35 :
    remainder2Coefficient5.coeff 35 =
      (2069187720024328570227264006657291355787421 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_36 :
    remainder2Coefficient5.coeff 36 =
      (-6686117133490773997916420110131588575194757 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_37 :
    remainder2Coefficient5.coeff 37 =
      (-15713983361751386062903313597586957964997198 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_38 :
    remainder2Coefficient5.coeff 38 =
      (108107639108100048200385184492677540844180312 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_39 :
    remainder2Coefficient5.coeff 39 =
      (-20984404370839676984211613442320871622164412 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_40 :
    remainder2Coefficient5.coeff 40 =
      (-1099916178960450575915685818529555687157919662 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_41 :
    remainder2Coefficient5.coeff 41 =
      (2396380361633016720239785833367126775002379437 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_42 :
    remainder2Coefficient5.coeff 42 =
      (5210269669951627349681283239449495527787077121 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_43 :
    remainder2Coefficient5.coeff 43 =
      (-31726243031577828134638573492632902354471093984 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_44 :
    remainder2Coefficient5.coeff 44 =
      (27161067309970447311973679620919266785043335179 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_45 :
    remainder2Coefficient5.coeff 45 =
      (178205050773421933199244930914495314572679868757 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_46 :
    remainder2Coefficient5.coeff 46 =
      (-596676247251947916726407473354347441926711917636 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_47 :
    remainder2Coefficient5.coeff 47 =
      (217432829839310336002817984518166135227832232782 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_48 :
    remainder2Coefficient5.coeff 48 =
      (3120093033409065786758827883803080316430806655045 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_49 :
    remainder2Coefficient5.coeff 49 =
      (-8665970048652318840432392931146127238888078672941 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
