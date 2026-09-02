/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData2
import Mathlib.Tactic.NormNum

/-!
# Recurrence 2 lookup certificate: A0 source coefficients, low half

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence2A0_coeff_0 :
    remainder2Coefficient0.coeff 0 =
      (0 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_1 :
    remainder2Coefficient0.coeff 1 =
      (0 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_2 :
    remainder2Coefficient0.coeff 2 =
      (1 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_3 :
    remainder2Coefficient0.coeff 3 =
      (21998 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_4 :
    remainder2Coefficient0.coeff 4 =
      (1213258 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_5 :
    remainder2Coefficient0.coeff 5 =
      (-6591719746 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_6 :
    remainder2Coefficient0.coeff 6 =
      (887174420015 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_7 :
    remainder2Coefficient0.coeff 7 =
      (10898850087779 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_8 :
    remainder2Coefficient0.coeff 8 =
      (-4242577921555076 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_9 :
    remainder2Coefficient0.coeff 9 =
      (-9044841330557190 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_10 :
    remainder2Coefficient0.coeff 10 =
      (5905879565633563356 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_11 :
    remainder2Coefficient0.coeff 11 =
      (73367409398595165996 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_12 :
    remainder2Coefficient0.coeff 12 =
      (-3131219520021488355261 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_13 :
    remainder2Coefficient0.coeff 13 =
      (-66505908255265167228909 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_14 :
    remainder2Coefficient0.coeff 14 =
      (409155522983929358223454 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_15 :
    remainder2Coefficient0.coeff 15 =
      (22027542795128115872321226 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_16 :
    remainder2Coefficient0.coeff 16 =
      (76735418560623238749227979 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_17 :
    remainder2Coefficient0.coeff 17 =
      (-3234018323272692008644959524 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_18 :
    remainder2Coefficient0.coeff 18 =
      (-29738389409425638678174724443 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_19 :
    remainder2Coefficient0.coeff 19 =
      (253887039826360477352885637974 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_20 :
    remainder2Coefficient0.coeff 20 =
      (3839461295707575052402511711145 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_21 :
    remainder2Coefficient0.coeff 21 =
      (-7632953412497286154928754530167 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_22 :
    remainder2Coefficient0.coeff 22 =
      (-325902109613993235482591511158062 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_23 :
    remainder2Coefficient0.coeff 23 =
      (-54189002951574352392486001446389 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_24 :
    remainder2Coefficient0.coeff 24 =
      (17939832588070721406987746062937250 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_25 :
    remainder2Coefficient0.coeff 25 =
      (31826313445941491054485986255887620 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_26 :
    remainder2Coefficient0.coeff 26 =
      (-849488679231132760490374031074814762 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_27 :
    remainder2Coefficient0.coeff 27 =
      (-1614355931044266796217772307414613716 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_28 :
    remainder2Coefficient0.coeff 28 =
      (31358151232828134232489089258528740581 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_29 :
    remainder2Coefficient0.coeff 29 =
      (59173772590237271321614902242554864604 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_30 :
    remainder2Coefficient0.coeff 30 =
      (-1037909449069702050995790634079279527234 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_31 :
    remainder2Coefficient0.coeff 31 =
      (-1165280355746439384243786350455420790049 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_32 :
    remainder2Coefficient0.coeff 32 =
      (28927249338570910072158119743920309724861 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_33 :
    remainder2Coefficient0.coeff 33 =
      (3724415618239167221623117838218836606730 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_34 :
    remainder2Coefficient0.coeff 34 =
      (-681578237840065642926261228656071824770362 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_35 :
    remainder2Coefficient0.coeff 35 =
      (762752762879364689572744288733998737444098 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_36 :
    remainder2Coefficient0.coeff 36 =
      (12747758848377365623179496199857217975063094 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_37 :
    remainder2Coefficient0.coeff 37 =
      (-33644919694007791905306165608311761387256527 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_38 :
    remainder2Coefficient0.coeff 38 =
      (-170616046135731321807523659719437449607831382 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_39 :
    remainder2Coefficient0.coeff 39 =
      (854731750744759183117612048451503577686718350 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_40 :
    remainder2Coefficient0.coeff 40 =
      (1070589103141380188990437600705938082237411849 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_41 :
    remainder2Coefficient0.coeff 41 =
      (-14533737069505132262481138493185774319227901666 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_42 :
    remainder2Coefficient0.coeff 42 =
      (14847492001852093904509154446647689144549047900 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_43 :
    remainder2Coefficient0.coeff 43 =
      (155606299034522954166844058198548068896279977537 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_44 :
    remainder2Coefficient0.coeff 44 =
      (-519630700961647778633579607877224146206648309539 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_45 :
    remainder2Coefficient0.coeff 45 =
      (-598801835612111105880235198090447628712531519493 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_46 :
    remainder2Coefficient0.coeff 46 =
      (6947902940277472273331017092804828544810974028139 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_47 :
    remainder2Coefficient0.coeff 47 =
      (-10475530471061913847079100899254638337734396287104 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_48 :
    remainder2Coefficient0.coeff 48 =
      (-40332554873310579622123872668669900409407948080662 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_49 :
    remainder2Coefficient0.coeff 49 =
      (193107590045649299339279328984668292960892819799483 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_50 :
    remainder2Coefficient0.coeff 50 =
      (-149432665535261992857347330551770721950842375691980 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_51 :
    remainder2Coefficient0.coeff 51 =
      (-1133497054982079041065679089970365931806088756989147 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_52 :
    remainder2Coefficient0.coeff 52 =
      (4040747699608870687257985013647732806121074286902738 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_53 :
    remainder2Coefficient0.coeff 53 =
      (-2785848571080064457962537035628974255157624433659535 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_54 :
    remainder2Coefficient0.coeff 54 =
      (-18687086537014865119121801645888755694124474167125176 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_55 :
    remainder2Coefficient0.coeff 55 =
      (66681838947911016521021237852219792660730576150126032 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_56 :
    remainder2Coefficient0.coeff 56 =
      (-74259866442592643309907716195443028789570438134352762 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_57 :
    remainder2Coefficient0.coeff 57 =
      (-147265800657316553789244740368621751889157008294390057 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_58 :
    remainder2Coefficient0.coeff 58 =
      (755349943097198560274645640023835200357276309089105499 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_59 :
    remainder2Coefficient0.coeff 59 =
      (-1379867726824908573819612208907630171932514084636054614 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
