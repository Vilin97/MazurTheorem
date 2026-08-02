/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData2
import Mathlib.Tactic.NormNum

/-!
# Recurrence 2 lookup certificate: A1 source coefficients, low half

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence2A1_coeff_0 :
    remainder2Coefficient1.coeff 0 =
      (0 : ℚ) := by
  unfold
    remainder2Coefficient1
    remainder2Coefficient1Block1
    remainder2Coefficient1Block0
    remainder2Coefficient1Chunk14
    remainder2Coefficient1Chunk13
    remainder2Coefficient1Chunk12
    remainder2Coefficient1Chunk11
    remainder2Coefficient1Chunk10
    remainder2Coefficient1Chunk9
    remainder2Coefficient1Chunk8
    remainder2Coefficient1Chunk7
    remainder2Coefficient1Chunk6
    remainder2Coefficient1Chunk5
    remainder2Coefficient1Chunk4
    remainder2Coefficient1Chunk3
    remainder2Coefficient1Chunk2
    remainder2Coefficient1Chunk1
    remainder2Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A1_coeff_1 :
    remainder2Coefficient1.coeff 1 =
      (0 : ℚ) := by
  unfold
    remainder2Coefficient1
    remainder2Coefficient1Block1
    remainder2Coefficient1Block0
    remainder2Coefficient1Chunk14
    remainder2Coefficient1Chunk13
    remainder2Coefficient1Chunk12
    remainder2Coefficient1Chunk11
    remainder2Coefficient1Chunk10
    remainder2Coefficient1Chunk9
    remainder2Coefficient1Chunk8
    remainder2Coefficient1Chunk7
    remainder2Coefficient1Chunk6
    remainder2Coefficient1Chunk5
    remainder2Coefficient1Chunk4
    remainder2Coefficient1Chunk3
    remainder2Coefficient1Chunk2
    remainder2Coefficient1Chunk1
    remainder2Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A1_coeff_2 :
    remainder2Coefficient1.coeff 2 =
      (-23 : ℚ) := by
  unfold
    remainder2Coefficient1
    remainder2Coefficient1Block1
    remainder2Coefficient1Block0
    remainder2Coefficient1Chunk14
    remainder2Coefficient1Chunk13
    remainder2Coefficient1Chunk12
    remainder2Coefficient1Chunk11
    remainder2Coefficient1Chunk10
    remainder2Coefficient1Chunk9
    remainder2Coefficient1Chunk8
    remainder2Coefficient1Chunk7
    remainder2Coefficient1Chunk6
    remainder2Coefficient1Chunk5
    remainder2Coefficient1Chunk4
    remainder2Coefficient1Chunk3
    remainder2Coefficient1Chunk2
    remainder2Coefficient1Chunk1
    remainder2Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A1_coeff_3 :
    remainder2Coefficient1.coeff 3 =
      (991446 : ℚ) := by
  unfold
    remainder2Coefficient1
    remainder2Coefficient1Block1
    remainder2Coefficient1Block0
    remainder2Coefficient1Chunk14
    remainder2Coefficient1Chunk13
    remainder2Coefficient1Chunk12
    remainder2Coefficient1Chunk11
    remainder2Coefficient1Chunk10
    remainder2Coefficient1Chunk9
    remainder2Coefficient1Chunk8
    remainder2Coefficient1Chunk7
    remainder2Coefficient1Chunk6
    remainder2Coefficient1Chunk5
    remainder2Coefficient1Chunk4
    remainder2Coefficient1Chunk3
    remainder2Coefficient1Chunk2
    remainder2Coefficient1Chunk1
    remainder2Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A1_coeff_4 :
    remainder2Coefficient1.coeff 4 =
      (34314719 : ℚ) := by
  unfold
    remainder2Coefficient1
    remainder2Coefficient1Block1
    remainder2Coefficient1Block0
    remainder2Coefficient1Chunk14
    remainder2Coefficient1Chunk13
    remainder2Coefficient1Chunk12
    remainder2Coefficient1Chunk11
    remainder2Coefficient1Chunk10
    remainder2Coefficient1Chunk9
    remainder2Coefficient1Chunk8
    remainder2Coefficient1Chunk7
    remainder2Coefficient1Chunk6
    remainder2Coefficient1Chunk5
    remainder2Coefficient1Chunk4
    remainder2Coefficient1Chunk3
    remainder2Coefficient1Chunk2
    remainder2Coefficient1Chunk1
    remainder2Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A1_coeff_5 :
    remainder2Coefficient1.coeff 5 =
      (-182010007593 : ℚ) := by
  unfold
    remainder2Coefficient1
    remainder2Coefficient1Block1
    remainder2Coefficient1Block0
    remainder2Coefficient1Chunk14
    remainder2Coefficient1Chunk13
    remainder2Coefficient1Chunk12
    remainder2Coefficient1Chunk11
    remainder2Coefficient1Chunk10
    remainder2Coefficient1Chunk9
    remainder2Coefficient1Chunk8
    remainder2Coefficient1Chunk7
    remainder2Coefficient1Chunk6
    remainder2Coefficient1Chunk5
    remainder2Coefficient1Chunk4
    remainder2Coefficient1Chunk3
    remainder2Coefficient1Chunk2
    remainder2Coefficient1Chunk1
    remainder2Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A1_coeff_6 :
    remainder2Coefficient1.coeff 6 =
      (12713487257368 : ℚ) := by
  unfold
    remainder2Coefficient1
    remainder2Coefficient1Block1
    remainder2Coefficient1Block0
    remainder2Coefficient1Chunk14
    remainder2Coefficient1Chunk13
    remainder2Coefficient1Chunk12
    remainder2Coefficient1Chunk11
    remainder2Coefficient1Chunk10
    remainder2Coefficient1Chunk9
    remainder2Coefficient1Chunk8
    remainder2Coefficient1Chunk7
    remainder2Coefficient1Chunk6
    remainder2Coefficient1Chunk5
    remainder2Coefficient1Chunk4
    remainder2Coefficient1Chunk3
    remainder2Coefficient1Chunk2
    remainder2Coefficient1Chunk1
    remainder2Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A1_coeff_7 :
    remainder2Coefficient1.coeff 7 =
      (809774120213950 : ℚ) := by
  unfold
    remainder2Coefficient1
    remainder2Coefficient1Block1
    remainder2Coefficient1Block0
    remainder2Coefficient1Chunk14
    remainder2Coefficient1Chunk13
    remainder2Coefficient1Chunk12
    remainder2Coefficient1Chunk11
    remainder2Coefficient1Chunk10
    remainder2Coefficient1Chunk9
    remainder2Coefficient1Chunk8
    remainder2Coefficient1Chunk7
    remainder2Coefficient1Chunk6
    remainder2Coefficient1Chunk5
    remainder2Coefficient1Chunk4
    remainder2Coefficient1Chunk3
    remainder2Coefficient1Chunk2
    remainder2Coefficient1Chunk1
    remainder2Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A1_coeff_8 :
    remainder2Coefficient1.coeff 8 =
      (-24940064428596179 : ℚ) := by
  unfold
    remainder2Coefficient1
    remainder2Coefficient1Block1
    remainder2Coefficient1Block0
    remainder2Coefficient1Chunk14
    remainder2Coefficient1Chunk13
    remainder2Coefficient1Chunk12
    remainder2Coefficient1Chunk11
    remainder2Coefficient1Chunk10
    remainder2Coefficient1Chunk9
    remainder2Coefficient1Chunk8
    remainder2Coefficient1Chunk7
    remainder2Coefficient1Chunk6
    remainder2Coefficient1Chunk5
    remainder2Coefficient1Chunk4
    remainder2Coefficient1Chunk3
    remainder2Coefficient1Chunk2
    remainder2Coefficient1Chunk1
    remainder2Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A1_coeff_9 :
    remainder2Coefficient1.coeff 9 =
      (-1511187499165252688 : ℚ) := by
  unfold
    remainder2Coefficient1
    remainder2Coefficient1Block1
    remainder2Coefficient1Block0
    remainder2Coefficient1Chunk14
    remainder2Coefficient1Chunk13
    remainder2Coefficient1Chunk12
    remainder2Coefficient1Chunk11
    remainder2Coefficient1Chunk10
    remainder2Coefficient1Chunk9
    remainder2Coefficient1Chunk8
    remainder2Coefficient1Chunk7
    remainder2Coefficient1Chunk6
    remainder2Coefficient1Chunk5
    remainder2Coefficient1Chunk4
    remainder2Coefficient1Chunk3
    remainder2Coefficient1Chunk2
    remainder2Coefficient1Chunk1
    remainder2Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A1_coeff_10 :
    remainder2Coefficient1.coeff 10 =
      (-1401006467656754001 : ℚ) := by
  unfold
    remainder2Coefficient1
    remainder2Coefficient1Block1
    remainder2Coefficient1Block0
    remainder2Coefficient1Chunk14
    remainder2Coefficient1Chunk13
    remainder2Coefficient1Chunk12
    remainder2Coefficient1Chunk11
    remainder2Coefficient1Chunk10
    remainder2Coefficient1Chunk9
    remainder2Coefficient1Chunk8
    remainder2Coefficient1Chunk7
    remainder2Coefficient1Chunk6
    remainder2Coefficient1Chunk5
    remainder2Coefficient1Chunk4
    remainder2Coefficient1Chunk3
    remainder2Coefficient1Chunk2
    remainder2Coefficient1Chunk1
    remainder2Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A1_coeff_11 :
    remainder2Coefficient1.coeff 11 =
      (1057485838428164119588 : ℚ) := by
  unfold
    remainder2Coefficient1
    remainder2Coefficient1Block1
    remainder2Coefficient1Block0
    remainder2Coefficient1Chunk14
    remainder2Coefficient1Chunk13
    remainder2Coefficient1Chunk12
    remainder2Coefficient1Chunk11
    remainder2Coefficient1Chunk10
    remainder2Coefficient1Chunk9
    remainder2Coefficient1Chunk8
    remainder2Coefficient1Chunk7
    remainder2Coefficient1Chunk6
    remainder2Coefficient1Chunk5
    remainder2Coefficient1Chunk4
    remainder2Coefficient1Chunk3
    remainder2Coefficient1Chunk2
    remainder2Coefficient1Chunk1
    remainder2Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A1_coeff_12 :
    remainder2Coefficient1.coeff 12 =
      (14904717066199156916092 : ℚ) := by
  unfold
    remainder2Coefficient1
    remainder2Coefficient1Block1
    remainder2Coefficient1Block0
    remainder2Coefficient1Chunk14
    remainder2Coefficient1Chunk13
    remainder2Coefficient1Chunk12
    remainder2Coefficient1Chunk11
    remainder2Coefficient1Chunk10
    remainder2Coefficient1Chunk9
    remainder2Coefficient1Chunk8
    remainder2Coefficient1Chunk7
    remainder2Coefficient1Chunk6
    remainder2Coefficient1Chunk5
    remainder2Coefficient1Chunk4
    remainder2Coefficient1Chunk3
    remainder2Coefficient1Chunk2
    remainder2Coefficient1Chunk1
    remainder2Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A1_coeff_13 :
    remainder2Coefficient1.coeff 13 =
      (-230250439109250632924208 : ℚ) := by
  unfold
    remainder2Coefficient1
    remainder2Coefficient1Block1
    remainder2Coefficient1Block0
    remainder2Coefficient1Chunk14
    remainder2Coefficient1Chunk13
    remainder2Coefficient1Chunk12
    remainder2Coefficient1Chunk11
    remainder2Coefficient1Chunk10
    remainder2Coefficient1Chunk9
    remainder2Coefficient1Chunk8
    remainder2Coefficient1Chunk7
    remainder2Coefficient1Chunk6
    remainder2Coefficient1Chunk5
    remainder2Coefficient1Chunk4
    remainder2Coefficient1Chunk3
    remainder2Coefficient1Chunk2
    remainder2Coefficient1Chunk1
    remainder2Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A1_coeff_14 :
    remainder2Coefficient1.coeff 14 =
      (-7159433264249329204390444 : ℚ) := by
  unfold
    remainder2Coefficient1
    remainder2Coefficient1Block1
    remainder2Coefficient1Block0
    remainder2Coefficient1Chunk14
    remainder2Coefficient1Chunk13
    remainder2Coefficient1Chunk12
    remainder2Coefficient1Chunk11
    remainder2Coefficient1Chunk10
    remainder2Coefficient1Chunk9
    remainder2Coefficient1Chunk8
    remainder2Coefficient1Chunk7
    remainder2Coefficient1Chunk6
    remainder2Coefficient1Chunk5
    remainder2Coefficient1Chunk4
    remainder2Coefficient1Chunk3
    remainder2Coefficient1Chunk2
    remainder2Coefficient1Chunk1
    remainder2Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A1_coeff_15 :
    remainder2Coefficient1.coeff 15 =
      (-800944141195000428913534 : ℚ) := by
  unfold
    remainder2Coefficient1
    remainder2Coefficient1Block1
    remainder2Coefficient1Block0
    remainder2Coefficient1Chunk14
    remainder2Coefficient1Chunk13
    remainder2Coefficient1Chunk12
    remainder2Coefficient1Chunk11
    remainder2Coefficient1Chunk10
    remainder2Coefficient1Chunk9
    remainder2Coefficient1Chunk8
    remainder2Coefficient1Chunk7
    remainder2Coefficient1Chunk6
    remainder2Coefficient1Chunk5
    remainder2Coefficient1Chunk4
    remainder2Coefficient1Chunk3
    remainder2Coefficient1Chunk2
    remainder2Coefficient1Chunk1
    remainder2Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A1_coeff_16 :
    remainder2Coefficient1.coeff 16 =
      (1336715720568965017819040794 : ℚ) := by
  unfold
    remainder2Coefficient1
    remainder2Coefficient1Block1
    remainder2Coefficient1Block0
    remainder2Coefficient1Chunk14
    remainder2Coefficient1Chunk13
    remainder2Coefficient1Chunk12
    remainder2Coefficient1Chunk11
    remainder2Coefficient1Chunk10
    remainder2Coefficient1Chunk9
    remainder2Coefficient1Chunk8
    remainder2Coefficient1Chunk7
    remainder2Coefficient1Chunk6
    remainder2Coefficient1Chunk5
    remainder2Coefficient1Chunk4
    remainder2Coefficient1Chunk3
    remainder2Coefficient1Chunk2
    remainder2Coefficient1Chunk1
    remainder2Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A1_coeff_17 :
    remainder2Coefficient1.coeff 17 =
      (9371219754866468327646862794 : ℚ) := by
  unfold
    remainder2Coefficient1
    remainder2Coefficient1Block1
    remainder2Coefficient1Block0
    remainder2Coefficient1Chunk14
    remainder2Coefficient1Chunk13
    remainder2Coefficient1Chunk12
    remainder2Coefficient1Chunk11
    remainder2Coefficient1Chunk10
    remainder2Coefficient1Chunk9
    remainder2Coefficient1Chunk8
    remainder2Coefficient1Chunk7
    remainder2Coefficient1Chunk6
    remainder2Coefficient1Chunk5
    remainder2Coefficient1Chunk4
    remainder2Coefficient1Chunk3
    remainder2Coefficient1Chunk2
    remainder2Coefficient1Chunk1
    remainder2Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A1_coeff_18 :
    remainder2Coefficient1.coeff 18 =
      (-152159977597680694262199235725 : ℚ) := by
  unfold
    remainder2Coefficient1
    remainder2Coefficient1Block1
    remainder2Coefficient1Block0
    remainder2Coefficient1Chunk14
    remainder2Coefficient1Chunk13
    remainder2Coefficient1Chunk12
    remainder2Coefficient1Chunk11
    remainder2Coefficient1Chunk10
    remainder2Coefficient1Chunk9
    remainder2Coefficient1Chunk8
    remainder2Coefficient1Chunk7
    remainder2Coefficient1Chunk6
    remainder2Coefficient1Chunk5
    remainder2Coefficient1Chunk4
    remainder2Coefficient1Chunk3
    remainder2Coefficient1Chunk2
    remainder2Coefficient1Chunk1
    remainder2Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A1_coeff_19 :
    remainder2Coefficient1.coeff 19 =
      (-1476675698552842302366816083544 : ℚ) := by
  unfold
    remainder2Coefficient1
    remainder2Coefficient1Block1
    remainder2Coefficient1Block0
    remainder2Coefficient1Chunk14
    remainder2Coefficient1Chunk13
    remainder2Coefficient1Chunk12
    remainder2Coefficient1Chunk11
    remainder2Coefficient1Chunk10
    remainder2Coefficient1Chunk9
    remainder2Coefficient1Chunk8
    remainder2Coefficient1Chunk7
    remainder2Coefficient1Chunk6
    remainder2Coefficient1Chunk5
    remainder2Coefficient1Chunk4
    remainder2Coefficient1Chunk3
    remainder2Coefficient1Chunk2
    remainder2Coefficient1Chunk1
    remainder2Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A1_coeff_20 :
    remainder2Coefficient1.coeff 20 =
      (7423831494855042805865550540966 : ℚ) := by
  unfold
    remainder2Coefficient1
    remainder2Coefficient1Block1
    remainder2Coefficient1Block0
    remainder2Coefficient1Chunk14
    remainder2Coefficient1Chunk13
    remainder2Coefficient1Chunk12
    remainder2Coefficient1Chunk11
    remainder2Coefficient1Chunk10
    remainder2Coefficient1Chunk9
    remainder2Coefficient1Chunk8
    remainder2Coefficient1Chunk7
    remainder2Coefficient1Chunk6
    remainder2Coefficient1Chunk5
    remainder2Coefficient1Chunk4
    remainder2Coefficient1Chunk3
    remainder2Coefficient1Chunk2
    remainder2Coefficient1Chunk1
    remainder2Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A1_coeff_21 :
    remainder2Coefficient1.coeff 21 =
      (166980362579297990515818353437658 : ℚ) := by
  unfold
    remainder2Coefficient1
    remainder2Coefficient1Block1
    remainder2Coefficient1Block0
    remainder2Coefficient1Chunk14
    remainder2Coefficient1Chunk13
    remainder2Coefficient1Chunk12
    remainder2Coefficient1Chunk11
    remainder2Coefficient1Chunk10
    remainder2Coefficient1Chunk9
    remainder2Coefficient1Chunk8
    remainder2Coefficient1Chunk7
    remainder2Coefficient1Chunk6
    remainder2Coefficient1Chunk5
    remainder2Coefficient1Chunk4
    remainder2Coefficient1Chunk3
    remainder2Coefficient1Chunk2
    remainder2Coefficient1Chunk1
    remainder2Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A1_coeff_22 :
    remainder2Coefficient1.coeff 22 =
      (-338050950523730163560503266156439 : ℚ) := by
  unfold
    remainder2Coefficient1
    remainder2Coefficient1Block1
    remainder2Coefficient1Block0
    remainder2Coefficient1Chunk14
    remainder2Coefficient1Chunk13
    remainder2Coefficient1Chunk12
    remainder2Coefficient1Chunk11
    remainder2Coefficient1Chunk10
    remainder2Coefficient1Chunk9
    remainder2Coefficient1Chunk8
    remainder2Coefficient1Chunk7
    remainder2Coefficient1Chunk6
    remainder2Coefficient1Chunk5
    remainder2Coefficient1Chunk4
    remainder2Coefficient1Chunk3
    remainder2Coefficient1Chunk2
    remainder2Coefficient1Chunk1
    remainder2Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A1_coeff_23 :
    remainder2Coefficient1.coeff 23 =
      (-10229350116733897326878981007695336 : ℚ) := by
  unfold
    remainder2Coefficient1
    remainder2Coefficient1Block1
    remainder2Coefficient1Block0
    remainder2Coefficient1Chunk14
    remainder2Coefficient1Chunk13
    remainder2Coefficient1Chunk12
    remainder2Coefficient1Chunk11
    remainder2Coefficient1Chunk10
    remainder2Coefficient1Chunk9
    remainder2Coefficient1Chunk8
    remainder2Coefficient1Chunk7
    remainder2Coefficient1Chunk6
    remainder2Coefficient1Chunk5
    remainder2Coefficient1Chunk4
    remainder2Coefficient1Chunk3
    remainder2Coefficient1Chunk2
    remainder2Coefficient1Chunk1
    remainder2Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A1_coeff_24 :
    remainder2Coefficient1.coeff 24 =
      (-2125560260375172499905965264154931 : ℚ) := by
  unfold
    remainder2Coefficient1
    remainder2Coefficient1Block1
    remainder2Coefficient1Block0
    remainder2Coefficient1Chunk14
    remainder2Coefficient1Chunk13
    remainder2Coefficient1Chunk12
    remainder2Coefficient1Chunk11
    remainder2Coefficient1Chunk10
    remainder2Coefficient1Chunk9
    remainder2Coefficient1Chunk8
    remainder2Coefficient1Chunk7
    remainder2Coefficient1Chunk6
    remainder2Coefficient1Chunk5
    remainder2Coefficient1Chunk4
    remainder2Coefficient1Chunk3
    remainder2Coefficient1Chunk2
    remainder2Coefficient1Chunk1
    remainder2Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A1_coeff_25 :
    remainder2Coefficient1.coeff 25 =
      (563370211501071328312802386841574086 : ℚ) := by
  unfold
    remainder2Coefficient1
    remainder2Coefficient1Block1
    remainder2Coefficient1Block0
    remainder2Coefficient1Chunk14
    remainder2Coefficient1Chunk13
    remainder2Coefficient1Chunk12
    remainder2Coefficient1Chunk11
    remainder2Coefficient1Chunk10
    remainder2Coefficient1Chunk9
    remainder2Coefficient1Chunk8
    remainder2Coefficient1Chunk7
    remainder2Coefficient1Chunk6
    remainder2Coefficient1Chunk5
    remainder2Coefficient1Chunk4
    remainder2Coefficient1Chunk3
    remainder2Coefficient1Chunk2
    remainder2Coefficient1Chunk1
    remainder2Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A1_coeff_26 :
    remainder2Coefficient1.coeff 26 =
      (268943619019748947580124367300453358 : ℚ) := by
  unfold
    remainder2Coefficient1
    remainder2Coefficient1Block1
    remainder2Coefficient1Block0
    remainder2Coefficient1Chunk14
    remainder2Coefficient1Chunk13
    remainder2Coefficient1Chunk12
    remainder2Coefficient1Chunk11
    remainder2Coefficient1Chunk10
    remainder2Coefficient1Chunk9
    remainder2Coefficient1Chunk8
    remainder2Coefficient1Chunk7
    remainder2Coefficient1Chunk6
    remainder2Coefficient1Chunk5
    remainder2Coefficient1Chunk4
    remainder2Coefficient1Chunk3
    remainder2Coefficient1Chunk2
    remainder2Coefficient1Chunk1
    remainder2Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A1_coeff_27 :
    remainder2Coefficient1.coeff 27 =
      (-22337226396841398490007237712497405760 : ℚ) := by
  unfold
    remainder2Coefficient1
    remainder2Coefficient1Block1
    remainder2Coefficient1Block0
    remainder2Coefficient1Chunk14
    remainder2Coefficient1Chunk13
    remainder2Coefficient1Chunk12
    remainder2Coefficient1Chunk11
    remainder2Coefficient1Chunk10
    remainder2Coefficient1Chunk9
    remainder2Coefficient1Chunk8
    remainder2Coefficient1Chunk7
    remainder2Coefficient1Chunk6
    remainder2Coefficient1Chunk5
    remainder2Coefficient1Chunk4
    remainder2Coefficient1Chunk3
    remainder2Coefficient1Chunk2
    remainder2Coefficient1Chunk1
    remainder2Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A1_coeff_28 :
    remainder2Coefficient1.coeff 28 =
      (-16302087361960395159433645119209771205 : ℚ) := by
  unfold
    remainder2Coefficient1
    remainder2Coefficient1Block1
    remainder2Coefficient1Block0
    remainder2Coefficient1Chunk14
    remainder2Coefficient1Chunk13
    remainder2Coefficient1Chunk12
    remainder2Coefficient1Chunk11
    remainder2Coefficient1Chunk10
    remainder2Coefficient1Chunk9
    remainder2Coefficient1Chunk8
    remainder2Coefficient1Chunk7
    remainder2Coefficient1Chunk6
    remainder2Coefficient1Chunk5
    remainder2Coefficient1Chunk4
    remainder2Coefficient1Chunk3
    remainder2Coefficient1Chunk2
    remainder2Coefficient1Chunk1
    remainder2Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A1_coeff_29 :
    remainder2Coefficient1.coeff 29 =
      (782884778513075620609733485006308898812 : ℚ) := by
  unfold
    remainder2Coefficient1
    remainder2Coefficient1Block1
    remainder2Coefficient1Block0
    remainder2Coefficient1Chunk14
    remainder2Coefficient1Chunk13
    remainder2Coefficient1Chunk12
    remainder2Coefficient1Chunk11
    remainder2Coefficient1Chunk10
    remainder2Coefficient1Chunk9
    remainder2Coefficient1Chunk8
    remainder2Coefficient1Chunk7
    remainder2Coefficient1Chunk6
    remainder2Coefficient1Chunk5
    remainder2Coefficient1Chunk4
    remainder2Coefficient1Chunk3
    remainder2Coefficient1Chunk2
    remainder2Coefficient1Chunk1
    remainder2Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A1_coeff_30 :
    remainder2Coefficient1.coeff 30 =
      (169100928911810487969607712933238095601 : ℚ) := by
  unfold
    remainder2Coefficient1
    remainder2Coefficient1Block1
    remainder2Coefficient1Block0
    remainder2Coefficient1Chunk14
    remainder2Coefficient1Chunk13
    remainder2Coefficient1Chunk12
    remainder2Coefficient1Chunk11
    remainder2Coefficient1Chunk10
    remainder2Coefficient1Chunk9
    remainder2Coefficient1Chunk8
    remainder2Coefficient1Chunk7
    remainder2Coefficient1Chunk6
    remainder2Coefficient1Chunk5
    remainder2Coefficient1Chunk4
    remainder2Coefficient1Chunk3
    remainder2Coefficient1Chunk2
    remainder2Coefficient1Chunk1
    remainder2Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A1_coeff_31 :
    remainder2Coefficient1.coeff 31 =
      (-22434483518242757074625435655352319831718 : ℚ) := by
  unfold
    remainder2Coefficient1
    remainder2Coefficient1Block1
    remainder2Coefficient1Block0
    remainder2Coefficient1Chunk14
    remainder2Coefficient1Chunk13
    remainder2Coefficient1Chunk12
    remainder2Coefficient1Chunk11
    remainder2Coefficient1Chunk10
    remainder2Coefficient1Chunk9
    remainder2Coefficient1Chunk8
    remainder2Coefficient1Chunk7
    remainder2Coefficient1Chunk6
    remainder2Coefficient1Chunk5
    remainder2Coefficient1Chunk4
    remainder2Coefficient1Chunk3
    remainder2Coefficient1Chunk2
    remainder2Coefficient1Chunk1
    remainder2Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A1_coeff_32 :
    remainder2Coefficient1.coeff 32 =
      (12149129729855203374463191490851350845219 : ℚ) := by
  unfold
    remainder2Coefficient1
    remainder2Coefficient1Block1
    remainder2Coefficient1Block0
    remainder2Coefficient1Chunk14
    remainder2Coefficient1Chunk13
    remainder2Coefficient1Chunk12
    remainder2Coefficient1Chunk11
    remainder2Coefficient1Chunk10
    remainder2Coefficient1Chunk9
    remainder2Coefficient1Chunk8
    remainder2Coefficient1Chunk7
    remainder2Coefficient1Chunk6
    remainder2Coefficient1Chunk5
    remainder2Coefficient1Chunk4
    remainder2Coefficient1Chunk3
    remainder2Coefficient1Chunk2
    remainder2Coefficient1Chunk1
    remainder2Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A1_coeff_33 :
    remainder2Coefficient1.coeff 33 =
      (537688842212710594891401914117782804026329 : ℚ) := by
  unfold
    remainder2Coefficient1
    remainder2Coefficient1Block1
    remainder2Coefficient1Block0
    remainder2Coefficient1Chunk14
    remainder2Coefficient1Chunk13
    remainder2Coefficient1Chunk12
    remainder2Coefficient1Chunk11
    remainder2Coefficient1Chunk10
    remainder2Coefficient1Chunk9
    remainder2Coefficient1Chunk8
    remainder2Coefficient1Chunk7
    remainder2Coefficient1Chunk6
    remainder2Coefficient1Chunk5
    remainder2Coefficient1Chunk4
    remainder2Coefficient1Chunk3
    remainder2Coefficient1Chunk2
    remainder2Coefficient1Chunk1
    remainder2Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A1_coeff_34 :
    remainder2Coefficient1.coeff 34 =
      (-866296460575465796670455267867388753669369 : ℚ) := by
  unfold
    remainder2Coefficient1
    remainder2Coefficient1Block1
    remainder2Coefficient1Block0
    remainder2Coefficient1Chunk14
    remainder2Coefficient1Chunk13
    remainder2Coefficient1Chunk12
    remainder2Coefficient1Chunk11
    remainder2Coefficient1Chunk10
    remainder2Coefficient1Chunk9
    remainder2Coefficient1Chunk8
    remainder2Coefficient1Chunk7
    remainder2Coefficient1Chunk6
    remainder2Coefficient1Chunk5
    remainder2Coefficient1Chunk4
    remainder2Coefficient1Chunk3
    remainder2Coefficient1Chunk2
    remainder2Coefficient1Chunk1
    remainder2Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A1_coeff_35 :
    remainder2Coefficient1.coeff 35 =
      (-10178800343993652398732960755834833985355521 : ℚ) := by
  unfold
    remainder2Coefficient1
    remainder2Coefficient1Block1
    remainder2Coefficient1Block0
    remainder2Coefficient1Chunk14
    remainder2Coefficient1Chunk13
    remainder2Coefficient1Chunk12
    remainder2Coefficient1Chunk11
    remainder2Coefficient1Chunk10
    remainder2Coefficient1Chunk9
    remainder2Coefficient1Chunk8
    remainder2Coefficient1Chunk7
    remainder2Coefficient1Chunk6
    remainder2Coefficient1Chunk5
    remainder2Coefficient1Chunk4
    remainder2Coefficient1Chunk3
    remainder2Coefficient1Chunk2
    remainder2Coefficient1Chunk1
    remainder2Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A1_coeff_36 :
    remainder2Coefficient1.coeff 36 =
      (30845305703298606992929688144684386050348722 : ℚ) := by
  unfold
    remainder2Coefficient1
    remainder2Coefficient1Block1
    remainder2Coefficient1Block0
    remainder2Coefficient1Chunk14
    remainder2Coefficient1Chunk13
    remainder2Coefficient1Chunk12
    remainder2Coefficient1Chunk11
    remainder2Coefficient1Chunk10
    remainder2Coefficient1Chunk9
    remainder2Coefficient1Chunk8
    remainder2Coefficient1Chunk7
    remainder2Coefficient1Chunk6
    remainder2Coefficient1Chunk5
    remainder2Coefficient1Chunk4
    remainder2Coefficient1Chunk3
    remainder2Coefficient1Chunk2
    remainder2Coefficient1Chunk1
    remainder2Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A1_coeff_37 :
    remainder2Coefficient1.coeff 37 =
      (138143825322861061374501546913615689092833736 : ℚ) := by
  unfold
    remainder2Coefficient1
    remainder2Coefficient1Block1
    remainder2Coefficient1Block0
    remainder2Coefficient1Chunk14
    remainder2Coefficient1Chunk13
    remainder2Coefficient1Chunk12
    remainder2Coefficient1Chunk11
    remainder2Coefficient1Chunk10
    remainder2Coefficient1Chunk9
    remainder2Coefficient1Chunk8
    remainder2Coefficient1Chunk7
    remainder2Coefficient1Chunk6
    remainder2Coefficient1Chunk5
    remainder2Coefficient1Chunk4
    remainder2Coefficient1Chunk3
    remainder2Coefficient1Chunk2
    remainder2Coefficient1Chunk1
    remainder2Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A1_coeff_38 :
    remainder2Coefficient1.coeff 38 =
      (-744345593375753309946174316548546440583310611 : ℚ) := by
  unfold
    remainder2Coefficient1
    remainder2Coefficient1Block1
    remainder2Coefficient1Block0
    remainder2Coefficient1Chunk14
    remainder2Coefficient1Chunk13
    remainder2Coefficient1Chunk12
    remainder2Coefficient1Chunk11
    remainder2Coefficient1Chunk10
    remainder2Coefficient1Chunk9
    remainder2Coefficient1Chunk8
    remainder2Coefficient1Chunk7
    remainder2Coefficient1Chunk6
    remainder2Coefficient1Chunk5
    remainder2Coefficient1Chunk4
    remainder2Coefficient1Chunk3
    remainder2Coefficient1Chunk2
    remainder2Coefficient1Chunk1
    remainder2Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A1_coeff_39 :
    remainder2Coefficient1.coeff 39 =
      (-895207211253094452398187469388442171570590165 : ℚ) := by
  unfold
    remainder2Coefficient1
    remainder2Coefficient1Block1
    remainder2Coefficient1Block0
    remainder2Coefficient1Chunk14
    remainder2Coefficient1Chunk13
    remainder2Coefficient1Chunk12
    remainder2Coefficient1Chunk11
    remainder2Coefficient1Chunk10
    remainder2Coefficient1Chunk9
    remainder2Coefficient1Chunk8
    remainder2Coefficient1Chunk7
    remainder2Coefficient1Chunk6
    remainder2Coefficient1Chunk5
    remainder2Coefficient1Chunk4
    remainder2Coefficient1Chunk3
    remainder2Coefficient1Chunk2
    remainder2Coefficient1Chunk1
    remainder2Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A1_coeff_40 :
    remainder2Coefficient1.coeff 40 =
      (12602628389526258851354891566204867902883476569 : ℚ) := by
  unfold
    remainder2Coefficient1
    remainder2Coefficient1Block1
    remainder2Coefficient1Block0
    remainder2Coefficient1Chunk14
    remainder2Coefficient1Chunk13
    remainder2Coefficient1Chunk12
    remainder2Coefficient1Chunk11
    remainder2Coefficient1Chunk10
    remainder2Coefficient1Chunk9
    remainder2Coefficient1Chunk8
    remainder2Coefficient1Chunk7
    remainder2Coefficient1Chunk6
    remainder2Coefficient1Chunk5
    remainder2Coefficient1Chunk4
    remainder2Coefficient1Chunk3
    remainder2Coefficient1Chunk2
    remainder2Coefficient1Chunk1
    remainder2Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A1_coeff_41 :
    remainder2Coefficient1.coeff 41 =
      (-11789716434675680598066479227024573301751833031 : ℚ) := by
  unfold
    remainder2Coefficient1
    remainder2Coefficient1Block1
    remainder2Coefficient1Block0
    remainder2Coefficient1Chunk14
    remainder2Coefficient1Chunk13
    remainder2Coefficient1Chunk12
    remainder2Coefficient1Chunk11
    remainder2Coefficient1Chunk10
    remainder2Coefficient1Chunk9
    remainder2Coefficient1Chunk8
    remainder2Coefficient1Chunk7
    remainder2Coefficient1Chunk6
    remainder2Coefficient1Chunk5
    remainder2Coefficient1Chunk4
    remainder2Coefficient1Chunk3
    remainder2Coefficient1Chunk2
    remainder2Coefficient1Chunk1
    remainder2Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A1_coeff_42 :
    remainder2Coefficient1.coeff 42 =
      (-139165872516838418896158854667393896510709872301 : ℚ) := by
  unfold
    remainder2Coefficient1
    remainder2Coefficient1Block1
    remainder2Coefficient1Block0
    remainder2Coefficient1Chunk14
    remainder2Coefficient1Chunk13
    remainder2Coefficient1Chunk12
    remainder2Coefficient1Chunk11
    remainder2Coefficient1Chunk10
    remainder2Coefficient1Chunk9
    remainder2Coefficient1Chunk8
    remainder2Coefficient1Chunk7
    remainder2Coefficient1Chunk6
    remainder2Coefficient1Chunk5
    remainder2Coefficient1Chunk4
    remainder2Coefficient1Chunk3
    remainder2Coefficient1Chunk2
    remainder2Coefficient1Chunk1
    remainder2Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A1_coeff_43 :
    remainder2Coefficient1.coeff 43 =
      (432112768142442353814148894616481470942321809786 : ℚ) := by
  unfold
    remainder2Coefficient1
    remainder2Coefficient1Block1
    remainder2Coefficient1Block0
    remainder2Coefficient1Chunk14
    remainder2Coefficient1Chunk13
    remainder2Coefficient1Chunk12
    remainder2Coefficient1Chunk11
    remainder2Coefficient1Chunk10
    remainder2Coefficient1Chunk9
    remainder2Coefficient1Chunk8
    remainder2Coefficient1Chunk7
    remainder2Coefficient1Chunk6
    remainder2Coefficient1Chunk5
    remainder2Coefficient1Chunk4
    remainder2Coefficient1Chunk3
    remainder2Coefficient1Chunk2
    remainder2Coefficient1Chunk1
    remainder2Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A1_coeff_44 :
    remainder2Coefficient1.coeff 44 =
      (648401638615966186456668747610539522190161225558 : ℚ) := by
  unfold
    remainder2Coefficient1
    remainder2Coefficient1Block1
    remainder2Coefficient1Block0
    remainder2Coefficient1Chunk14
    remainder2Coefficient1Chunk13
    remainder2Coefficient1Chunk12
    remainder2Coefficient1Chunk11
    remainder2Coefficient1Chunk10
    remainder2Coefficient1Chunk9
    remainder2Coefficient1Chunk8
    remainder2Coefficient1Chunk7
    remainder2Coefficient1Chunk6
    remainder2Coefficient1Chunk5
    remainder2Coefficient1Chunk4
    remainder2Coefficient1Chunk3
    remainder2Coefficient1Chunk2
    remainder2Coefficient1Chunk1
    remainder2Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A1_coeff_45 :
    remainder2Coefficient1.coeff 45 =
      (-6037767278326563296666525835768529343305035119745 : ℚ) := by
  unfold
    remainder2Coefficient1
    remainder2Coefficient1Block1
    remainder2Coefficient1Block0
    remainder2Coefficient1Chunk14
    remainder2Coefficient1Chunk13
    remainder2Coefficient1Chunk12
    remainder2Coefficient1Chunk11
    remainder2Coefficient1Chunk10
    remainder2Coefficient1Chunk9
    remainder2Coefficient1Chunk8
    remainder2Coefficient1Chunk7
    remainder2Coefficient1Chunk6
    remainder2Coefficient1Chunk5
    remainder2Coefficient1Chunk4
    remainder2Coefficient1Chunk3
    remainder2Coefficient1Chunk2
    remainder2Coefficient1Chunk1
    remainder2Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A1_coeff_46 :
    remainder2Coefficient1.coeff 46 =
      (7319164040280728673013255566132109193578495146294 : ℚ) := by
  unfold
    remainder2Coefficient1
    remainder2Coefficient1Block1
    remainder2Coefficient1Block0
    remainder2Coefficient1Chunk14
    remainder2Coefficient1Chunk13
    remainder2Coefficient1Chunk12
    remainder2Coefficient1Chunk11
    remainder2Coefficient1Chunk10
    remainder2Coefficient1Chunk9
    remainder2Coefficient1Chunk8
    remainder2Coefficient1Chunk7
    remainder2Coefficient1Chunk6
    remainder2Coefficient1Chunk5
    remainder2Coefficient1Chunk4
    remainder2Coefficient1Chunk3
    remainder2Coefficient1Chunk2
    remainder2Coefficient1Chunk1
    remainder2Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A1_coeff_47 :
    remainder2Coefficient1.coeff 47 =
      (39376151809298759682298403303322297574478351376786 : ℚ) := by
  unfold
    remainder2Coefficient1
    remainder2Coefficient1Block1
    remainder2Coefficient1Block0
    remainder2Coefficient1Chunk14
    remainder2Coefficient1Chunk13
    remainder2Coefficient1Chunk12
    remainder2Coefficient1Chunk11
    remainder2Coefficient1Chunk10
    remainder2Coefficient1Chunk9
    remainder2Coefficient1Chunk8
    remainder2Coefficient1Chunk7
    remainder2Coefficient1Chunk6
    remainder2Coefficient1Chunk5
    remainder2Coefficient1Chunk4
    remainder2Coefficient1Chunk3
    remainder2Coefficient1Chunk2
    remainder2Coefficient1Chunk1
    remainder2Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A1_coeff_48 :
    remainder2Coefficient1.coeff 48 =
      (-158544148055671054942981428221540990703068279312848 : ℚ) := by
  unfold
    remainder2Coefficient1
    remainder2Coefficient1Block1
    remainder2Coefficient1Block0
    remainder2Coefficient1Chunk14
    remainder2Coefficient1Chunk13
    remainder2Coefficient1Chunk12
    remainder2Coefficient1Chunk11
    remainder2Coefficient1Chunk10
    remainder2Coefficient1Chunk9
    remainder2Coefficient1Chunk8
    remainder2Coefficient1Chunk7
    remainder2Coefficient1Chunk6
    remainder2Coefficient1Chunk5
    remainder2Coefficient1Chunk4
    remainder2Coefficient1Chunk3
    remainder2Coefficient1Chunk2
    remainder2Coefficient1Chunk1
    remainder2Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A1_coeff_49 :
    remainder2Coefficient1.coeff 49 =
      (63358724873144633399933389938629023169622069684614 : ℚ) := by
  unfold
    remainder2Coefficient1
    remainder2Coefficient1Block1
    remainder2Coefficient1Block0
    remainder2Coefficient1Chunk14
    remainder2Coefficient1Chunk13
    remainder2Coefficient1Chunk12
    remainder2Coefficient1Chunk11
    remainder2Coefficient1Chunk10
    remainder2Coefficient1Chunk9
    remainder2Coefficient1Chunk8
    remainder2Coefficient1Chunk7
    remainder2Coefficient1Chunk6
    remainder2Coefficient1Chunk5
    remainder2Coefficient1Chunk4
    remainder2Coefficient1Chunk3
    remainder2Coefficient1Chunk2
    remainder2Coefficient1Chunk1
    remainder2Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A1_coeff_50 :
    remainder2Coefficient1.coeff 50 =
      (1064558347078202935519998281089920262378412868830515 : ℚ) := by
  unfold
    remainder2Coefficient1
    remainder2Coefficient1Block1
    remainder2Coefficient1Block0
    remainder2Coefficient1Chunk14
    remainder2Coefficient1Chunk13
    remainder2Coefficient1Chunk12
    remainder2Coefficient1Chunk11
    remainder2Coefficient1Chunk10
    remainder2Coefficient1Chunk9
    remainder2Coefficient1Chunk8
    remainder2Coefficient1Chunk7
    remainder2Coefficient1Chunk6
    remainder2Coefficient1Chunk5
    remainder2Coefficient1Chunk4
    remainder2Coefficient1Chunk3
    remainder2Coefficient1Chunk2
    remainder2Coefficient1Chunk1
    remainder2Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A1_coeff_51 :
    remainder2Coefficient1.coeff 51 =
      (-3146619741164609779553998395203135504539567542823798 : ℚ) := by
  unfold
    remainder2Coefficient1
    remainder2Coefficient1Block1
    remainder2Coefficient1Block0
    remainder2Coefficient1Chunk14
    remainder2Coefficient1Chunk13
    remainder2Coefficient1Chunk12
    remainder2Coefficient1Chunk11
    remainder2Coefficient1Chunk10
    remainder2Coefficient1Chunk9
    remainder2Coefficient1Chunk8
    remainder2Coefficient1Chunk7
    remainder2Coefficient1Chunk6
    remainder2Coefficient1Chunk5
    remainder2Coefficient1Chunk4
    remainder2Coefficient1Chunk3
    remainder2Coefficient1Chunk2
    remainder2Coefficient1Chunk1
    remainder2Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A1_coeff_52 :
    remainder2Coefficient1.coeff 52 =
      (876307759424208137110477158844935261665956234512959 : ℚ) := by
  unfold
    remainder2Coefficient1
    remainder2Coefficient1Block1
    remainder2Coefficient1Block0
    remainder2Coefficient1Chunk14
    remainder2Coefficient1Chunk13
    remainder2Coefficient1Chunk12
    remainder2Coefficient1Chunk11
    remainder2Coefficient1Chunk10
    remainder2Coefficient1Chunk9
    remainder2Coefficient1Chunk8
    remainder2Coefficient1Chunk7
    remainder2Coefficient1Chunk6
    remainder2Coefficient1Chunk5
    remainder2Coefficient1Chunk4
    remainder2Coefficient1Chunk3
    remainder2Coefficient1Chunk2
    remainder2Coefficient1Chunk1
    remainder2Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A1_coeff_53 :
    remainder2Coefficient1.coeff 53 =
      (17552225484796966209684620157723463839167888348993832 : ℚ) := by
  unfold
    remainder2Coefficient1
    remainder2Coefficient1Block1
    remainder2Coefficient1Block0
    remainder2Coefficient1Chunk14
    remainder2Coefficient1Chunk13
    remainder2Coefficient1Chunk12
    remainder2Coefficient1Chunk11
    remainder2Coefficient1Chunk10
    remainder2Coefficient1Chunk9
    remainder2Coefficient1Chunk8
    remainder2Coefficient1Chunk7
    remainder2Coefficient1Chunk6
    remainder2Coefficient1Chunk5
    remainder2Coefficient1Chunk4
    remainder2Coefficient1Chunk3
    remainder2Coefficient1Chunk2
    remainder2Coefficient1Chunk1
    remainder2Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A1_coeff_54 :
    remainder2Coefficient1.coeff 54 =
      (-51060801395036558645419750914266778279505713183364077 : ℚ) := by
  unfold
    remainder2Coefficient1
    remainder2Coefficient1Block1
    remainder2Coefficient1Block0
    remainder2Coefficient1Chunk14
    remainder2Coefficient1Chunk13
    remainder2Coefficient1Chunk12
    remainder2Coefficient1Chunk11
    remainder2Coefficient1Chunk10
    remainder2Coefficient1Chunk9
    remainder2Coefficient1Chunk8
    remainder2Coefficient1Chunk7
    remainder2Coefficient1Chunk6
    remainder2Coefficient1Chunk5
    remainder2Coefficient1Chunk4
    remainder2Coefficient1Chunk3
    remainder2Coefficient1Chunk2
    remainder2Coefficient1Chunk1
    remainder2Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A1_coeff_55 :
    remainder2Coefficient1.coeff 55 =
      (38708632590349550038909320209836313832035801399688659 : ℚ) := by
  unfold
    remainder2Coefficient1
    remainder2Coefficient1Block1
    remainder2Coefficient1Block0
    remainder2Coefficient1Chunk14
    remainder2Coefficient1Chunk13
    remainder2Coefficient1Chunk12
    remainder2Coefficient1Chunk11
    remainder2Coefficient1Chunk10
    remainder2Coefficient1Chunk9
    remainder2Coefficient1Chunk8
    remainder2Coefficient1Chunk7
    remainder2Coefficient1Chunk6
    remainder2Coefficient1Chunk5
    remainder2Coefficient1Chunk4
    remainder2Coefficient1Chunk3
    remainder2Coefficient1Chunk2
    remainder2Coefficient1Chunk1
    remainder2Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A1_coeff_56 :
    remainder2Coefficient1.coeff 56 =
      (156122700235894541215359928419238137620803549708792141 : ℚ) := by
  unfold
    remainder2Coefficient1
    remainder2Coefficient1Block1
    remainder2Coefficient1Block0
    remainder2Coefficient1Chunk14
    remainder2Coefficient1Chunk13
    remainder2Coefficient1Chunk12
    remainder2Coefficient1Chunk11
    remainder2Coefficient1Chunk10
    remainder2Coefficient1Chunk9
    remainder2Coefficient1Chunk8
    remainder2Coefficient1Chunk7
    remainder2Coefficient1Chunk6
    remainder2Coefficient1Chunk5
    remainder2Coefficient1Chunk4
    remainder2Coefficient1Chunk3
    remainder2Coefficient1Chunk2
    remainder2Coefficient1Chunk1
    remainder2Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A1_coeff_57 :
    remainder2Coefficient1.coeff 57 =
      (-595906504110546317847580435390630519293736106243862022 : ℚ) := by
  unfold
    remainder2Coefficient1
    remainder2Coefficient1Block1
    remainder2Coefficient1Block0
    remainder2Coefficient1Chunk14
    remainder2Coefficient1Chunk13
    remainder2Coefficient1Chunk12
    remainder2Coefficient1Chunk11
    remainder2Coefficient1Chunk10
    remainder2Coefficient1Chunk9
    remainder2Coefficient1Chunk8
    remainder2Coefficient1Chunk7
    remainder2Coefficient1Chunk6
    remainder2Coefficient1Chunk5
    remainder2Coefficient1Chunk4
    remainder2Coefficient1Chunk3
    remainder2Coefficient1Chunk2
    remainder2Coefficient1Chunk1
    remainder2Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
