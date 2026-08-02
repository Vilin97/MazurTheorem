/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData2
import Mathlib.Tactic.NormNum

/-!
# Recurrence 2 lookup certificate: A3 source coefficients, low half

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence2A3_coeff_0 :
    remainder2Coefficient3.coeff 0 =
      (0 : ℚ) := by
  unfold
    remainder2Coefficient3
    remainder2Coefficient3Block1
    remainder2Coefficient3Block0
    remainder2Coefficient3Chunk13
    remainder2Coefficient3Chunk12
    remainder2Coefficient3Chunk11
    remainder2Coefficient3Chunk10
    remainder2Coefficient3Chunk9
    remainder2Coefficient3Chunk8
    remainder2Coefficient3Chunk7
    remainder2Coefficient3Chunk6
    remainder2Coefficient3Chunk5
    remainder2Coefficient3Chunk4
    remainder2Coefficient3Chunk3
    remainder2Coefficient3Chunk2
    remainder2Coefficient3Chunk1
    remainder2Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A3_coeff_1 :
    remainder2Coefficient3.coeff 1 =
      (-60 : ℚ) := by
  unfold
    remainder2Coefficient3
    remainder2Coefficient3Block1
    remainder2Coefficient3Block0
    remainder2Coefficient3Chunk13
    remainder2Coefficient3Chunk12
    remainder2Coefficient3Chunk11
    remainder2Coefficient3Chunk10
    remainder2Coefficient3Chunk9
    remainder2Coefficient3Chunk8
    remainder2Coefficient3Chunk7
    remainder2Coefficient3Chunk6
    remainder2Coefficient3Chunk5
    remainder2Coefficient3Chunk4
    remainder2Coefficient3Chunk3
    remainder2Coefficient3Chunk2
    remainder2Coefficient3Chunk1
    remainder2Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A3_coeff_2 :
    remainder2Coefficient3.coeff 2 =
      (144992 : ℚ) := by
  unfold
    remainder2Coefficient3
    remainder2Coefficient3Block1
    remainder2Coefficient3Block0
    remainder2Coefficient3Chunk13
    remainder2Coefficient3Chunk12
    remainder2Coefficient3Chunk11
    remainder2Coefficient3Chunk10
    remainder2Coefficient3Chunk9
    remainder2Coefficient3Chunk8
    remainder2Coefficient3Chunk7
    remainder2Coefficient3Chunk6
    remainder2Coefficient3Chunk5
    remainder2Coefficient3Chunk4
    remainder2Coefficient3Chunk3
    remainder2Coefficient3Chunk2
    remainder2Coefficient3Chunk1
    remainder2Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A3_coeff_3 :
    remainder2Coefficient3.coeff 3 =
      (337210200 : ℚ) := by
  unfold
    remainder2Coefficient3
    remainder2Coefficient3Block1
    remainder2Coefficient3Block0
    remainder2Coefficient3Chunk13
    remainder2Coefficient3Chunk12
    remainder2Coefficient3Chunk11
    remainder2Coefficient3Chunk10
    remainder2Coefficient3Chunk9
    remainder2Coefficient3Chunk8
    remainder2Coefficient3Chunk7
    remainder2Coefficient3Chunk6
    remainder2Coefficient3Chunk5
    remainder2Coefficient3Chunk4
    remainder2Coefficient3Chunk3
    remainder2Coefficient3Chunk2
    remainder2Coefficient3Chunk1
    remainder2Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A3_coeff_4 :
    remainder2Coefficient3.coeff 4 =
      (-114233123413 : ℚ) := by
  unfold
    remainder2Coefficient3
    remainder2Coefficient3Block1
    remainder2Coefficient3Block0
    remainder2Coefficient3Chunk13
    remainder2Coefficient3Chunk12
    remainder2Coefficient3Chunk11
    remainder2Coefficient3Chunk10
    remainder2Coefficient3Chunk9
    remainder2Coefficient3Chunk8
    remainder2Coefficient3Chunk7
    remainder2Coefficient3Chunk6
    remainder2Coefficient3Chunk5
    remainder2Coefficient3Chunk4
    remainder2Coefficient3Chunk3
    remainder2Coefficient3Chunk2
    remainder2Coefficient3Chunk1
    remainder2Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A3_coeff_5 :
    remainder2Coefficient3.coeff 5 =
      (-1446040827081 : ℚ) := by
  unfold
    remainder2Coefficient3
    remainder2Coefficient3Block1
    remainder2Coefficient3Block0
    remainder2Coefficient3Chunk13
    remainder2Coefficient3Chunk12
    remainder2Coefficient3Chunk11
    remainder2Coefficient3Chunk10
    remainder2Coefficient3Chunk9
    remainder2Coefficient3Chunk8
    remainder2Coefficient3Chunk7
    remainder2Coefficient3Chunk6
    remainder2Coefficient3Chunk5
    remainder2Coefficient3Chunk4
    remainder2Coefficient3Chunk3
    remainder2Coefficient3Chunk2
    remainder2Coefficient3Chunk1
    remainder2Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A3_coeff_6 :
    remainder2Coefficient3.coeff 6 =
      (1120623009347098 : ℚ) := by
  unfold
    remainder2Coefficient3
    remainder2Coefficient3Block1
    remainder2Coefficient3Block0
    remainder2Coefficient3Chunk13
    remainder2Coefficient3Chunk12
    remainder2Coefficient3Chunk11
    remainder2Coefficient3Chunk10
    remainder2Coefficient3Chunk9
    remainder2Coefficient3Chunk8
    remainder2Coefficient3Chunk7
    remainder2Coefficient3Chunk6
    remainder2Coefficient3Chunk5
    remainder2Coefficient3Chunk4
    remainder2Coefficient3Chunk3
    remainder2Coefficient3Chunk2
    remainder2Coefficient3Chunk1
    remainder2Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A3_coeff_7 :
    remainder2Coefficient3.coeff 7 =
      (-6226391170151878 : ℚ) := by
  unfold
    remainder2Coefficient3
    remainder2Coefficient3Block1
    remainder2Coefficient3Block0
    remainder2Coefficient3Chunk13
    remainder2Coefficient3Chunk12
    remainder2Coefficient3Chunk11
    remainder2Coefficient3Chunk10
    remainder2Coefficient3Chunk9
    remainder2Coefficient3Chunk8
    remainder2Coefficient3Chunk7
    remainder2Coefficient3Chunk6
    remainder2Coefficient3Chunk5
    remainder2Coefficient3Chunk4
    remainder2Coefficient3Chunk3
    remainder2Coefficient3Chunk2
    remainder2Coefficient3Chunk1
    remainder2Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A3_coeff_8 :
    remainder2Coefficient3.coeff 8 =
      (-1890393992552803819 : ℚ) := by
  unfold
    remainder2Coefficient3
    remainder2Coefficient3Block1
    remainder2Coefficient3Block0
    remainder2Coefficient3Chunk13
    remainder2Coefficient3Chunk12
    remainder2Coefficient3Chunk11
    remainder2Coefficient3Chunk10
    remainder2Coefficient3Chunk9
    remainder2Coefficient3Chunk8
    remainder2Coefficient3Chunk7
    remainder2Coefficient3Chunk6
    remainder2Coefficient3Chunk5
    remainder2Coefficient3Chunk4
    remainder2Coefficient3Chunk3
    remainder2Coefficient3Chunk2
    remainder2Coefficient3Chunk1
    remainder2Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A3_coeff_9 :
    remainder2Coefficient3.coeff 9 =
      (-7664712791670880689 : ℚ) := by
  unfold
    remainder2Coefficient3
    remainder2Coefficient3Block1
    remainder2Coefficient3Block0
    remainder2Coefficient3Chunk13
    remainder2Coefficient3Chunk12
    remainder2Coefficient3Chunk11
    remainder2Coefficient3Chunk10
    remainder2Coefficient3Chunk9
    remainder2Coefficient3Chunk8
    remainder2Coefficient3Chunk7
    remainder2Coefficient3Chunk6
    remainder2Coefficient3Chunk5
    remainder2Coefficient3Chunk4
    remainder2Coefficient3Chunk3
    remainder2Coefficient3Chunk2
    remainder2Coefficient3Chunk1
    remainder2Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A3_coeff_10 :
    remainder2Coefficient3.coeff 10 =
      (1186110264949517701774 : ℚ) := by
  unfold
    remainder2Coefficient3
    remainder2Coefficient3Block1
    remainder2Coefficient3Block0
    remainder2Coefficient3Chunk13
    remainder2Coefficient3Chunk12
    remainder2Coefficient3Chunk11
    remainder2Coefficient3Chunk10
    remainder2Coefficient3Chunk9
    remainder2Coefficient3Chunk8
    remainder2Coefficient3Chunk7
    remainder2Coefficient3Chunk6
    remainder2Coefficient3Chunk5
    remainder2Coefficient3Chunk4
    remainder2Coefficient3Chunk3
    remainder2Coefficient3Chunk2
    remainder2Coefficient3Chunk1
    remainder2Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A3_coeff_11 :
    remainder2Coefficient3.coeff 11 =
      (14495384085042601774868 : ℚ) := by
  unfold
    remainder2Coefficient3
    remainder2Coefficient3Block1
    remainder2Coefficient3Block0
    remainder2Coefficient3Chunk13
    remainder2Coefficient3Chunk12
    remainder2Coefficient3Chunk11
    remainder2Coefficient3Chunk10
    remainder2Coefficient3Chunk9
    remainder2Coefficient3Chunk8
    remainder2Coefficient3Chunk7
    remainder2Coefficient3Chunk6
    remainder2Coefficient3Chunk5
    remainder2Coefficient3Chunk4
    remainder2Coefficient3Chunk3
    remainder2Coefficient3Chunk2
    remainder2Coefficient3Chunk1
    remainder2Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A3_coeff_12 :
    remainder2Coefficient3.coeff 12 =
      (-323012681716189718208053 : ℚ) := by
  unfold
    remainder2Coefficient3
    remainder2Coefficient3Block1
    remainder2Coefficient3Block0
    remainder2Coefficient3Chunk13
    remainder2Coefficient3Chunk12
    remainder2Coefficient3Chunk11
    remainder2Coefficient3Chunk10
    remainder2Coefficient3Chunk9
    remainder2Coefficient3Chunk8
    remainder2Coefficient3Chunk7
    remainder2Coefficient3Chunk6
    remainder2Coefficient3Chunk5
    remainder2Coefficient3Chunk4
    remainder2Coefficient3Chunk3
    remainder2Coefficient3Chunk2
    remainder2Coefficient3Chunk1
    remainder2Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A3_coeff_13 :
    remainder2Coefficient3.coeff 13 =
      (-5350675907080725328279101 : ℚ) := by
  unfold
    remainder2Coefficient3
    remainder2Coefficient3Block1
    remainder2Coefficient3Block0
    remainder2Coefficient3Chunk13
    remainder2Coefficient3Chunk12
    remainder2Coefficient3Chunk11
    remainder2Coefficient3Chunk10
    remainder2Coefficient3Chunk9
    remainder2Coefficient3Chunk8
    remainder2Coefficient3Chunk7
    remainder2Coefficient3Chunk6
    remainder2Coefficient3Chunk5
    remainder2Coefficient3Chunk4
    remainder2Coefficient3Chunk3
    remainder2Coefficient3Chunk2
    remainder2Coefficient3Chunk1
    remainder2Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A3_coeff_14 :
    remainder2Coefficient3.coeff 14 =
      (19081312682070323987420769 : ℚ) := by
  unfold
    remainder2Coefficient3
    remainder2Coefficient3Block1
    remainder2Coefficient3Block0
    remainder2Coefficient3Chunk13
    remainder2Coefficient3Chunk12
    remainder2Coefficient3Chunk11
    remainder2Coefficient3Chunk10
    remainder2Coefficient3Chunk9
    remainder2Coefficient3Chunk8
    remainder2Coefficient3Chunk7
    remainder2Coefficient3Chunk6
    remainder2Coefficient3Chunk5
    remainder2Coefficient3Chunk4
    remainder2Coefficient3Chunk3
    remainder2Coefficient3Chunk2
    remainder2Coefficient3Chunk1
    remainder2Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A3_coeff_15 :
    remainder2Coefficient3.coeff 15 =
      (1205027831713483381382352925 : ℚ) := by
  unfold
    remainder2Coefficient3
    remainder2Coefficient3Block1
    remainder2Coefficient3Block0
    remainder2Coefficient3Chunk13
    remainder2Coefficient3Chunk12
    remainder2Coefficient3Chunk11
    remainder2Coefficient3Chunk10
    remainder2Coefficient3Chunk9
    remainder2Coefficient3Chunk8
    remainder2Coefficient3Chunk7
    remainder2Coefficient3Chunk6
    remainder2Coefficient3Chunk5
    remainder2Coefficient3Chunk4
    remainder2Coefficient3Chunk3
    remainder2Coefficient3Chunk2
    remainder2Coefficient3Chunk1
    remainder2Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A3_coeff_16 :
    remainder2Coefficient3.coeff 16 =
      (-54569879067551627558148355 : ℚ) := by
  unfold
    remainder2Coefficient3
    remainder2Coefficient3Block1
    remainder2Coefficient3Block0
    remainder2Coefficient3Chunk13
    remainder2Coefficient3Chunk12
    remainder2Coefficient3Chunk11
    remainder2Coefficient3Chunk10
    remainder2Coefficient3Chunk9
    remainder2Coefficient3Chunk8
    remainder2Coefficient3Chunk7
    remainder2Coefficient3Chunk6
    remainder2Coefficient3Chunk5
    remainder2Coefficient3Chunk4
    remainder2Coefficient3Chunk3
    remainder2Coefficient3Chunk2
    remainder2Coefficient3Chunk1
    remainder2Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A3_coeff_17 :
    remainder2Coefficient3.coeff 17 =
      (-101571790718327454660827242646 : ℚ) := by
  unfold
    remainder2Coefficient3
    remainder2Coefficient3Block1
    remainder2Coefficient3Block0
    remainder2Coefficient3Chunk13
    remainder2Coefficient3Chunk12
    remainder2Coefficient3Chunk11
    remainder2Coefficient3Chunk10
    remainder2Coefficient3Chunk9
    remainder2Coefficient3Chunk8
    remainder2Coefficient3Chunk7
    remainder2Coefficient3Chunk6
    remainder2Coefficient3Chunk5
    remainder2Coefficient3Chunk4
    remainder2Coefficient3Chunk3
    remainder2Coefficient3Chunk2
    remainder2Coefficient3Chunk1
    remainder2Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A3_coeff_18 :
    remainder2Coefficient3.coeff 18 =
      (-650549405351974257520118427995 : ℚ) := by
  unfold
    remainder2Coefficient3
    remainder2Coefficient3Block1
    remainder2Coefficient3Block0
    remainder2Coefficient3Chunk13
    remainder2Coefficient3Chunk12
    remainder2Coefficient3Chunk11
    remainder2Coefficient3Chunk10
    remainder2Coefficient3Chunk9
    remainder2Coefficient3Chunk8
    remainder2Coefficient3Chunk7
    remainder2Coefficient3Chunk6
    remainder2Coefficient3Chunk5
    remainder2Coefficient3Chunk4
    remainder2Coefficient3Chunk3
    remainder2Coefficient3Chunk2
    remainder2Coefficient3Chunk1
    remainder2Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A3_coeff_19 :
    remainder2Coefficient3.coeff 19 =
      (9227650503192677672918781534744 : ℚ) := by
  unfold
    remainder2Coefficient3
    remainder2Coefficient3Block1
    remainder2Coefficient3Block0
    remainder2Coefficient3Chunk13
    remainder2Coefficient3Chunk12
    remainder2Coefficient3Chunk11
    remainder2Coefficient3Chunk10
    remainder2Coefficient3Chunk9
    remainder2Coefficient3Chunk8
    remainder2Coefficient3Chunk7
    remainder2Coefficient3Chunk6
    remainder2Coefficient3Chunk5
    remainder2Coefficient3Chunk4
    remainder2Coefficient3Chunk3
    remainder2Coefficient3Chunk2
    remainder2Coefficient3Chunk1
    remainder2Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A3_coeff_20 :
    remainder2Coefficient3.coeff 20 =
      (46104552010704738459147239845351 : ℚ) := by
  unfold
    remainder2Coefficient3
    remainder2Coefficient3Block1
    remainder2Coefficient3Block0
    remainder2Coefficient3Chunk13
    remainder2Coefficient3Chunk12
    remainder2Coefficient3Chunk11
    remainder2Coefficient3Chunk10
    remainder2Coefficient3Chunk9
    remainder2Coefficient3Chunk8
    remainder2Coefficient3Chunk7
    remainder2Coefficient3Chunk6
    remainder2Coefficient3Chunk5
    remainder2Coefficient3Chunk4
    remainder2Coefficient3Chunk3
    remainder2Coefficient3Chunk2
    remainder2Coefficient3Chunk1
    remainder2Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A3_coeff_21 :
    remainder2Coefficient3.coeff 21 =
      (-355895040729730830597860482259151 : ℚ) := by
  unfold
    remainder2Coefficient3
    remainder2Coefficient3Block1
    remainder2Coefficient3Block0
    remainder2Coefficient3Chunk13
    remainder2Coefficient3Chunk12
    remainder2Coefficient3Chunk11
    remainder2Coefficient3Chunk10
    remainder2Coefficient3Chunk9
    remainder2Coefficient3Chunk8
    remainder2Coefficient3Chunk7
    remainder2Coefficient3Chunk6
    remainder2Coefficient3Chunk5
    remainder2Coefficient3Chunk4
    remainder2Coefficient3Chunk3
    remainder2Coefficient3Chunk2
    remainder2Coefficient3Chunk1
    remainder2Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A3_coeff_22 :
    remainder2Coefficient3.coeff 22 =
      (-3770195349740932032386184257945046 : ℚ) := by
  unfold
    remainder2Coefficient3
    remainder2Coefficient3Block1
    remainder2Coefficient3Block0
    remainder2Coefficient3Chunk13
    remainder2Coefficient3Chunk12
    remainder2Coefficient3Chunk11
    remainder2Coefficient3Chunk10
    remainder2Coefficient3Chunk9
    remainder2Coefficient3Chunk8
    remainder2Coefficient3Chunk7
    remainder2Coefficient3Chunk6
    remainder2Coefficient3Chunk5
    remainder2Coefficient3Chunk4
    remainder2Coefficient3Chunk3
    remainder2Coefficient3Chunk2
    remainder2Coefficient3Chunk1
    remainder2Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A3_coeff_23 :
    remainder2Coefficient3.coeff 23 =
      (17502796376348235058891317421237394 : ℚ) := by
  unfold
    remainder2Coefficient3
    remainder2Coefficient3Block1
    remainder2Coefficient3Block0
    remainder2Coefficient3Chunk13
    remainder2Coefficient3Chunk12
    remainder2Coefficient3Chunk11
    remainder2Coefficient3Chunk10
    remainder2Coefficient3Chunk9
    remainder2Coefficient3Chunk8
    remainder2Coefficient3Chunk7
    remainder2Coefficient3Chunk6
    remainder2Coefficient3Chunk5
    remainder2Coefficient3Chunk4
    remainder2Coefficient3Chunk3
    remainder2Coefficient3Chunk2
    remainder2Coefficient3Chunk1
    remainder2Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A3_coeff_24 :
    remainder2Coefficient3.coeff 24 =
      (155940408479648275346173351208713541 : ℚ) := by
  unfold
    remainder2Coefficient3
    remainder2Coefficient3Block1
    remainder2Coefficient3Block0
    remainder2Coefficient3Chunk13
    remainder2Coefficient3Chunk12
    remainder2Coefficient3Chunk11
    remainder2Coefficient3Chunk10
    remainder2Coefficient3Chunk9
    remainder2Coefficient3Chunk8
    remainder2Coefficient3Chunk7
    remainder2Coefficient3Chunk6
    remainder2Coefficient3Chunk5
    remainder2Coefficient3Chunk4
    remainder2Coefficient3Chunk3
    remainder2Coefficient3Chunk2
    remainder2Coefficient3Chunk1
    remainder2Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A3_coeff_25 :
    remainder2Coefficient3.coeff 25 =
      (-539992111689709489806039449053330902 : ℚ) := by
  unfold
    remainder2Coefficient3
    remainder2Coefficient3Block1
    remainder2Coefficient3Block0
    remainder2Coefficient3Chunk13
    remainder2Coefficient3Chunk12
    remainder2Coefficient3Chunk11
    remainder2Coefficient3Chunk10
    remainder2Coefficient3Chunk9
    remainder2Coefficient3Chunk8
    remainder2Coefficient3Chunk7
    remainder2Coefficient3Chunk6
    remainder2Coefficient3Chunk5
    remainder2Coefficient3Chunk4
    remainder2Coefficient3Chunk3
    remainder2Coefficient3Chunk2
    remainder2Coefficient3Chunk1
    remainder2Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A3_coeff_26 :
    remainder2Coefficient3.coeff 26 =
      (-5891690741671953724981053994148980820 : ℚ) := by
  unfold
    remainder2Coefficient3
    remainder2Coefficient3Block1
    remainder2Coefficient3Block0
    remainder2Coefficient3Chunk13
    remainder2Coefficient3Chunk12
    remainder2Coefficient3Chunk11
    remainder2Coefficient3Chunk10
    remainder2Coefficient3Chunk9
    remainder2Coefficient3Chunk8
    remainder2Coefficient3Chunk7
    remainder2Coefficient3Chunk6
    remainder2Coefficient3Chunk5
    remainder2Coefficient3Chunk4
    remainder2Coefficient3Chunk3
    remainder2Coefficient3Chunk2
    remainder2Coefficient3Chunk1
    remainder2Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A3_coeff_27 :
    remainder2Coefficient3.coeff 27 =
      (19364984958319004293618854497598764168 : ℚ) := by
  unfold
    remainder2Coefficient3
    remainder2Coefficient3Block1
    remainder2Coefficient3Block0
    remainder2Coefficient3Chunk13
    remainder2Coefficient3Chunk12
    remainder2Coefficient3Chunk11
    remainder2Coefficient3Chunk10
    remainder2Coefficient3Chunk9
    remainder2Coefficient3Chunk8
    remainder2Coefficient3Chunk7
    remainder2Coefficient3Chunk6
    remainder2Coefficient3Chunk5
    remainder2Coefficient3Chunk4
    remainder2Coefficient3Chunk3
    remainder2Coefficient3Chunk2
    remainder2Coefficient3Chunk1
    remainder2Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A3_coeff_28 :
    remainder2Coefficient3.coeff 28 =
      (161459061594926880905641512579200311762 : ℚ) := by
  unfold
    remainder2Coefficient3
    remainder2Coefficient3Block1
    remainder2Coefficient3Block0
    remainder2Coefficient3Chunk13
    remainder2Coefficient3Chunk12
    remainder2Coefficient3Chunk11
    remainder2Coefficient3Chunk10
    remainder2Coefficient3Chunk9
    remainder2Coefficient3Chunk8
    remainder2Coefficient3Chunk7
    remainder2Coefficient3Chunk6
    remainder2Coefficient3Chunk5
    remainder2Coefficient3Chunk4
    remainder2Coefficient3Chunk3
    remainder2Coefficient3Chunk2
    remainder2Coefficient3Chunk1
    remainder2Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A3_coeff_29 :
    remainder2Coefficient3.coeff 29 =
      (-602614607404782543474794065438144304736 : ℚ) := by
  unfold
    remainder2Coefficient3
    remainder2Coefficient3Block1
    remainder2Coefficient3Block0
    remainder2Coefficient3Chunk13
    remainder2Coefficient3Chunk12
    remainder2Coefficient3Chunk11
    remainder2Coefficient3Chunk10
    remainder2Coefficient3Chunk9
    remainder2Coefficient3Chunk8
    remainder2Coefficient3Chunk7
    remainder2Coefficient3Chunk6
    remainder2Coefficient3Chunk5
    remainder2Coefficient3Chunk4
    remainder2Coefficient3Chunk3
    remainder2Coefficient3Chunk2
    remainder2Coefficient3Chunk1
    remainder2Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A3_coeff_30 :
    remainder2Coefficient3.coeff 30 =
      (-3554003684411565316456393508546234911994 : ℚ) := by
  unfold
    remainder2Coefficient3
    remainder2Coefficient3Block1
    remainder2Coefficient3Block0
    remainder2Coefficient3Chunk13
    remainder2Coefficient3Chunk12
    remainder2Coefficient3Chunk11
    remainder2Coefficient3Chunk10
    remainder2Coefficient3Chunk9
    remainder2Coefficient3Chunk8
    remainder2Coefficient3Chunk7
    remainder2Coefficient3Chunk6
    remainder2Coefficient3Chunk5
    remainder2Coefficient3Chunk4
    remainder2Coefficient3Chunk3
    remainder2Coefficient3Chunk2
    remainder2Coefficient3Chunk1
    remainder2Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A3_coeff_31 :
    remainder2Coefficient3.coeff 31 =
      (17255211102769595505069781743533790106948 : ℚ) := by
  unfold
    remainder2Coefficient3
    remainder2Coefficient3Block1
    remainder2Coefficient3Block0
    remainder2Coefficient3Chunk13
    remainder2Coefficient3Chunk12
    remainder2Coefficient3Chunk11
    remainder2Coefficient3Chunk10
    remainder2Coefficient3Chunk9
    remainder2Coefficient3Chunk8
    remainder2Coefficient3Chunk7
    remainder2Coefficient3Chunk6
    remainder2Coefficient3Chunk5
    remainder2Coefficient3Chunk4
    remainder2Coefficient3Chunk3
    remainder2Coefficient3Chunk2
    remainder2Coefficient3Chunk1
    remainder2Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A3_coeff_32 :
    remainder2Coefficient3.coeff 32 =
      (55384268122777797849118807530568108578721 : ℚ) := by
  unfold
    remainder2Coefficient3
    remainder2Coefficient3Block1
    remainder2Coefficient3Block0
    remainder2Coefficient3Chunk13
    remainder2Coefficient3Chunk12
    remainder2Coefficient3Chunk11
    remainder2Coefficient3Chunk10
    remainder2Coefficient3Chunk9
    remainder2Coefficient3Chunk8
    remainder2Coefficient3Chunk7
    remainder2Coefficient3Chunk6
    remainder2Coefficient3Chunk5
    remainder2Coefficient3Chunk4
    remainder2Coefficient3Chunk3
    remainder2Coefficient3Chunk2
    remainder2Coefficient3Chunk1
    remainder2Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A3_coeff_33 :
    remainder2Coefficient3.coeff 33 =
      (-408975986341552459375411106638462660105392 : ℚ) := by
  unfold
    remainder2Coefficient3
    remainder2Coefficient3Block1
    remainder2Coefficient3Block0
    remainder2Coefficient3Chunk13
    remainder2Coefficient3Chunk12
    remainder2Coefficient3Chunk11
    remainder2Coefficient3Chunk10
    remainder2Coefficient3Chunk9
    remainder2Coefficient3Chunk8
    remainder2Coefficient3Chunk7
    remainder2Coefficient3Chunk6
    remainder2Coefficient3Chunk5
    remainder2Coefficient3Chunk4
    remainder2Coefficient3Chunk3
    remainder2Coefficient3Chunk2
    remainder2Coefficient3Chunk1
    remainder2Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A3_coeff_34 :
    remainder2Coefficient3.coeff 34 =
      (-429472406512399769223982788343766418493177 : ℚ) := by
  unfold
    remainder2Coefficient3
    remainder2Coefficient3Block1
    remainder2Coefficient3Block0
    remainder2Coefficient3Chunk13
    remainder2Coefficient3Chunk12
    remainder2Coefficient3Chunk11
    remainder2Coefficient3Chunk10
    remainder2Coefficient3Chunk9
    remainder2Coefficient3Chunk8
    remainder2Coefficient3Chunk7
    remainder2Coefficient3Chunk6
    remainder2Coefficient3Chunk5
    remainder2Coefficient3Chunk4
    remainder2Coefficient3Chunk3
    remainder2Coefficient3Chunk2
    remainder2Coefficient3Chunk1
    remainder2Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A3_coeff_35 :
    remainder2Coefficient3.coeff 35 =
      (7636922589519785821039428126710304963391474 : ℚ) := by
  unfold
    remainder2Coefficient3
    remainder2Coefficient3Block1
    remainder2Coefficient3Block0
    remainder2Coefficient3Chunk13
    remainder2Coefficient3Chunk12
    remainder2Coefficient3Chunk11
    remainder2Coefficient3Chunk10
    remainder2Coefficient3Chunk9
    remainder2Coefficient3Chunk8
    remainder2Coefficient3Chunk7
    remainder2Coefficient3Chunk6
    remainder2Coefficient3Chunk5
    remainder2Coefficient3Chunk4
    remainder2Coefficient3Chunk3
    remainder2Coefficient3Chunk2
    remainder2Coefficient3Chunk1
    remainder2Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A3_coeff_36 :
    remainder2Coefficient3.coeff 36 =
      (-5972615649185960823655997056577502238520819 : ℚ) := by
  unfold
    remainder2Coefficient3
    remainder2Coefficient3Block1
    remainder2Coefficient3Block0
    remainder2Coefficient3Chunk13
    remainder2Coefficient3Chunk12
    remainder2Coefficient3Chunk11
    remainder2Coefficient3Chunk10
    remainder2Coefficient3Chunk9
    remainder2Coefficient3Chunk8
    remainder2Coefficient3Chunk7
    remainder2Coefficient3Chunk6
    remainder2Coefficient3Chunk5
    remainder2Coefficient3Chunk4
    remainder2Coefficient3Chunk3
    remainder2Coefficient3Chunk2
    remainder2Coefficient3Chunk1
    remainder2Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A3_coeff_37 :
    remainder2Coefficient3.coeff 37 =
      (-103196802034186994620357192376772393313934948 : ℚ) := by
  unfold
    remainder2Coefficient3
    remainder2Coefficient3Block1
    remainder2Coefficient3Block0
    remainder2Coefficient3Chunk13
    remainder2Coefficient3Chunk12
    remainder2Coefficient3Chunk11
    remainder2Coefficient3Chunk10
    remainder2Coefficient3Chunk9
    remainder2Coefficient3Chunk8
    remainder2Coefficient3Chunk7
    remainder2Coefficient3Chunk6
    remainder2Coefficient3Chunk5
    remainder2Coefficient3Chunk4
    remainder2Coefficient3Chunk3
    remainder2Coefficient3Chunk2
    remainder2Coefficient3Chunk1
    remainder2Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A3_coeff_38 :
    remainder2Coefficient3.coeff 38 =
      (278531489455583671983182498987984801222166978 : ℚ) := by
  unfold
    remainder2Coefficient3
    remainder2Coefficient3Block1
    remainder2Coefficient3Block0
    remainder2Coefficient3Chunk13
    remainder2Coefficient3Chunk12
    remainder2Coefficient3Chunk11
    remainder2Coefficient3Chunk10
    remainder2Coefficient3Chunk9
    remainder2Coefficient3Chunk8
    remainder2Coefficient3Chunk7
    remainder2Coefficient3Chunk6
    remainder2Coefficient3Chunk5
    remainder2Coefficient3Chunk4
    remainder2Coefficient3Chunk3
    remainder2Coefficient3Chunk2
    remainder2Coefficient3Chunk1
    remainder2Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A3_coeff_39 :
    remainder2Coefficient3.coeff 39 =
      (802671472616779569307783777750692615093839523 : ℚ) := by
  unfold
    remainder2Coefficient3
    remainder2Coefficient3Block1
    remainder2Coefficient3Block0
    remainder2Coefficient3Chunk13
    remainder2Coefficient3Chunk12
    remainder2Coefficient3Chunk11
    remainder2Coefficient3Chunk10
    remainder2Coefficient3Chunk9
    remainder2Coefficient3Chunk8
    remainder2Coefficient3Chunk7
    remainder2Coefficient3Chunk6
    remainder2Coefficient3Chunk5
    remainder2Coefficient3Chunk4
    remainder2Coefficient3Chunk3
    remainder2Coefficient3Chunk2
    remainder2Coefficient3Chunk1
    remainder2Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A3_coeff_40 :
    remainder2Coefficient3.coeff 40 =
      (-5095472275444967680452415046527764847424531289 : ℚ) := by
  unfold
    remainder2Coefficient3
    remainder2Coefficient3Block1
    remainder2Coefficient3Block0
    remainder2Coefficient3Chunk13
    remainder2Coefficient3Chunk12
    remainder2Coefficient3Chunk11
    remainder2Coefficient3Chunk10
    remainder2Coefficient3Chunk9
    remainder2Coefficient3Chunk8
    remainder2Coefficient3Chunk7
    remainder2Coefficient3Chunk6
    remainder2Coefficient3Chunk5
    remainder2Coefficient3Chunk4
    remainder2Coefficient3Chunk3
    remainder2Coefficient3Chunk2
    remainder2Coefficient3Chunk1
    remainder2Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A3_coeff_41 :
    remainder2Coefficient3.coeff 41 =
      (1616550411635808977878116633631418844750306089 : ℚ) := by
  unfold
    remainder2Coefficient3
    remainder2Coefficient3Block1
    remainder2Coefficient3Block0
    remainder2Coefficient3Chunk13
    remainder2Coefficient3Chunk12
    remainder2Coefficient3Chunk11
    remainder2Coefficient3Chunk10
    remainder2Coefficient3Chunk9
    remainder2Coefficient3Chunk8
    remainder2Coefficient3Chunk7
    remainder2Coefficient3Chunk6
    remainder2Coefficient3Chunk5
    remainder2Coefficient3Chunk4
    remainder2Coefficient3Chunk3
    remainder2Coefficient3Chunk2
    remainder2Coefficient3Chunk1
    remainder2Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A3_coeff_42 :
    remainder2Coefficient3.coeff 42 =
      (51990963322906723698998517920121619253352666777 : ℚ) := by
  unfold
    remainder2Coefficient3
    remainder2Coefficient3Block1
    remainder2Coefficient3Block0
    remainder2Coefficient3Chunk13
    remainder2Coefficient3Chunk12
    remainder2Coefficient3Chunk11
    remainder2Coefficient3Chunk10
    remainder2Coefficient3Chunk9
    remainder2Coefficient3Chunk8
    remainder2Coefficient3Chunk7
    remainder2Coefficient3Chunk6
    remainder2Coefficient3Chunk5
    remainder2Coefficient3Chunk4
    remainder2Coefficient3Chunk3
    remainder2Coefficient3Chunk2
    remainder2Coefficient3Chunk1
    remainder2Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A3_coeff_43 :
    remainder2Coefficient3.coeff 43 =
      (-134953349921645771473991539178865612758973748641 : ℚ) := by
  unfold
    remainder2Coefficient3
    remainder2Coefficient3Block1
    remainder2Coefficient3Block0
    remainder2Coefficient3Chunk13
    remainder2Coefficient3Chunk12
    remainder2Coefficient3Chunk11
    remainder2Coefficient3Chunk10
    remainder2Coefficient3Chunk9
    remainder2Coefficient3Chunk8
    remainder2Coefficient3Chunk7
    remainder2Coefficient3Chunk6
    remainder2Coefficient3Chunk5
    remainder2Coefficient3Chunk4
    remainder2Coefficient3Chunk3
    remainder2Coefficient3Chunk2
    remainder2Coefficient3Chunk1
    remainder2Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A3_coeff_44 :
    remainder2Coefficient3.coeff 44 =
      (-186243573966169544428262160522130926648718617077 : ℚ) := by
  unfold
    remainder2Coefficient3
    remainder2Coefficient3Block1
    remainder2Coefficient3Block0
    remainder2Coefficient3Chunk13
    remainder2Coefficient3Chunk12
    remainder2Coefficient3Chunk11
    remainder2Coefficient3Chunk10
    remainder2Coefficient3Chunk9
    remainder2Coefficient3Chunk8
    remainder2Coefficient3Chunk7
    remainder2Coefficient3Chunk6
    remainder2Coefficient3Chunk5
    remainder2Coefficient3Chunk4
    remainder2Coefficient3Chunk3
    remainder2Coefficient3Chunk2
    remainder2Coefficient3Chunk1
    remainder2Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A3_coeff_45 :
    remainder2Coefficient3.coeff 45 =
      (1666429559828701409885735644943615103733639282975 : ℚ) := by
  unfold
    remainder2Coefficient3
    remainder2Coefficient3Block1
    remainder2Coefficient3Block0
    remainder2Coefficient3Chunk13
    remainder2Coefficient3Chunk12
    remainder2Coefficient3Chunk11
    remainder2Coefficient3Chunk10
    remainder2Coefficient3Chunk9
    remainder2Coefficient3Chunk8
    remainder2Coefficient3Chunk7
    remainder2Coefficient3Chunk6
    remainder2Coefficient3Chunk5
    remainder2Coefficient3Chunk4
    remainder2Coefficient3Chunk3
    remainder2Coefficient3Chunk2
    remainder2Coefficient3Chunk1
    remainder2Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A3_coeff_46 :
    remainder2Coefficient3.coeff 46 =
      (-2466916198420109254297779917252601204358032259112 : ℚ) := by
  unfold
    remainder2Coefficient3
    remainder2Coefficient3Block1
    remainder2Coefficient3Block0
    remainder2Coefficient3Chunk13
    remainder2Coefficient3Chunk12
    remainder2Coefficient3Chunk11
    remainder2Coefficient3Chunk10
    remainder2Coefficient3Chunk9
    remainder2Coefficient3Chunk8
    remainder2Coefficient3Chunk7
    remainder2Coefficient3Chunk6
    remainder2Coefficient3Chunk5
    remainder2Coefficient3Chunk4
    remainder2Coefficient3Chunk3
    remainder2Coefficient3Chunk2
    remainder2Coefficient3Chunk1
    remainder2Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A3_coeff_47 :
    remainder2Coefficient3.coeff 47 =
      (-7193139565494378284995111613989859487638048123699 : ℚ) := by
  unfold
    remainder2Coefficient3
    remainder2Coefficient3Block1
    remainder2Coefficient3Block0
    remainder2Coefficient3Chunk13
    remainder2Coefficient3Chunk12
    remainder2Coefficient3Chunk11
    remainder2Coefficient3Chunk10
    remainder2Coefficient3Chunk9
    remainder2Coefficient3Chunk8
    remainder2Coefficient3Chunk7
    remainder2Coefficient3Chunk6
    remainder2Coefficient3Chunk5
    remainder2Coefficient3Chunk4
    remainder2Coefficient3Chunk3
    remainder2Coefficient3Chunk2
    remainder2Coefficient3Chunk1
    remainder2Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A3_coeff_48 :
    remainder2Coefficient3.coeff 48 =
      (36471586247137802510340750755657550865252238338051 : ℚ) := by
  unfold
    remainder2Coefficient3
    remainder2Coefficient3Block1
    remainder2Coefficient3Block0
    remainder2Coefficient3Chunk13
    remainder2Coefficient3Chunk12
    remainder2Coefficient3Chunk11
    remainder2Coefficient3Chunk10
    remainder2Coefficient3Chunk9
    remainder2Coefficient3Chunk8
    remainder2Coefficient3Chunk7
    remainder2Coefficient3Chunk6
    remainder2Coefficient3Chunk5
    remainder2Coefficient3Chunk4
    remainder2Coefficient3Chunk3
    remainder2Coefficient3Chunk2
    remainder2Coefficient3Chunk1
    remainder2Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A3_coeff_49 :
    remainder2Coefficient3.coeff 49 =
      (-42344753845482499724650697994842686063694746861454 : ℚ) := by
  unfold
    remainder2Coefficient3
    remainder2Coefficient3Block1
    remainder2Coefficient3Block0
    remainder2Coefficient3Chunk13
    remainder2Coefficient3Chunk12
    remainder2Coefficient3Chunk11
    remainder2Coefficient3Chunk10
    remainder2Coefficient3Chunk9
    remainder2Coefficient3Chunk8
    remainder2Coefficient3Chunk7
    remainder2Coefficient3Chunk6
    remainder2Coefficient3Chunk5
    remainder2Coefficient3Chunk4
    remainder2Coefficient3Chunk3
    remainder2Coefficient3Chunk2
    remainder2Coefficient3Chunk1
    remainder2Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A3_coeff_50 :
    remainder2Coefficient3.coeff 50 =
      (-129417700013243732828864495397861779997637217283505 : ℚ) := by
  unfold
    remainder2Coefficient3
    remainder2Coefficient3Block1
    remainder2Coefficient3Block0
    remainder2Coefficient3Chunk13
    remainder2Coefficient3Chunk12
    remainder2Coefficient3Chunk11
    remainder2Coefficient3Chunk10
    remainder2Coefficient3Chunk9
    remainder2Coefficient3Chunk8
    remainder2Coefficient3Chunk7
    remainder2Coefficient3Chunk6
    remainder2Coefficient3Chunk5
    remainder2Coefficient3Chunk4
    remainder2Coefficient3Chunk3
    remainder2Coefficient3Chunk2
    remainder2Coefficient3Chunk1
    remainder2Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A3_coeff_51 :
    remainder2Coefficient3.coeff 51 =
      (592882251057240725870784756053567465215899867346951 : ℚ) := by
  unfold
    remainder2Coefficient3
    remainder2Coefficient3Block1
    remainder2Coefficient3Block0
    remainder2Coefficient3Chunk13
    remainder2Coefficient3Chunk12
    remainder2Coefficient3Chunk11
    remainder2Coefficient3Chunk10
    remainder2Coefficient3Chunk9
    remainder2Coefficient3Chunk8
    remainder2Coefficient3Chunk7
    remainder2Coefficient3Chunk6
    remainder2Coefficient3Chunk5
    remainder2Coefficient3Chunk4
    remainder2Coefficient3Chunk3
    remainder2Coefficient3Chunk2
    remainder2Coefficient3Chunk1
    remainder2Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A3_coeff_52 :
    remainder2Coefficient3.coeff 52 =
      (-813491307248877463559718692386536313840641770494930 : ℚ) := by
  unfold
    remainder2Coefficient3
    remainder2Coefficient3Block1
    remainder2Coefficient3Block0
    remainder2Coefficient3Chunk13
    remainder2Coefficient3Chunk12
    remainder2Coefficient3Chunk11
    remainder2Coefficient3Chunk10
    remainder2Coefficient3Chunk9
    remainder2Coefficient3Chunk8
    remainder2Coefficient3Chunk7
    remainder2Coefficient3Chunk6
    remainder2Coefficient3Chunk5
    remainder2Coefficient3Chunk4
    remainder2Coefficient3Chunk3
    remainder2Coefficient3Chunk2
    remainder2Coefficient3Chunk1
    remainder2Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A3_coeff_53 :
    remainder2Coefficient3.coeff 53 =
      (-981393607761442560978477872434481245809405708939563 : ℚ) := by
  unfold
    remainder2Coefficient3
    remainder2Coefficient3Block1
    remainder2Coefficient3Block0
    remainder2Coefficient3Chunk13
    remainder2Coefficient3Chunk12
    remainder2Coefficient3Chunk11
    remainder2Coefficient3Chunk10
    remainder2Coefficient3Chunk9
    remainder2Coefficient3Chunk8
    remainder2Coefficient3Chunk7
    remainder2Coefficient3Chunk6
    remainder2Coefficient3Chunk5
    remainder2Coefficient3Chunk4
    remainder2Coefficient3Chunk3
    remainder2Coefficient3Chunk2
    remainder2Coefficient3Chunk1
    remainder2Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
