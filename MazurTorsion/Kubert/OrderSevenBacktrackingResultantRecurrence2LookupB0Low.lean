/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData2
import Mathlib.Tactic.NormNum

/-!
# Recurrence 2 lookup certificate: B0 source coefficients, low half

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence2B0_coeff_0 :
    remainder3Coefficient0.coeff 0 =
      (0 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_1 :
    remainder3Coefficient0.coeff 1 =
      (0 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_2 :
    remainder3Coefficient0.coeff 2 =
      (-8 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_3 :
    remainder3Coefficient0.coeff 3 =
      (179024 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_4 :
    remainder3Coefficient0.coeff 4 =
      (30754666 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_5 :
    remainder3Coefficient0.coeff 5 =
      (477021417487 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_6 :
    remainder3Coefficient0.coeff 6 =
      (-232679923019180 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_7 :
    remainder3Coefficient0.coeff 7 =
      (101440949732911807 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_8 :
    remainder3Coefficient0.coeff 8 =
      (-24730814056414366604 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_9 :
    remainder3Coefficient0.coeff 9 =
      (4024008953500262585477 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_10 :
    remainder3Coefficient0.coeff 10 =
      (-453727011615361254128640 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_11 :
    remainder3Coefficient0.coeff 11 =
      (35773836854796317297182412 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_12 :
    remainder3Coefficient0.coeff 12 =
      (-2034870664052154352728358965 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_13 :
    remainder3Coefficient0.coeff 13 =
      (83905281819788621191507714267 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_14 :
    remainder3Coefficient0.coeff 14 =
      (-2629889589502770617695121931036 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_15 :
    remainder3Coefficient0.coeff 15 =
      (68870813236477147681526337937965 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_16 :
    remainder3Coefficient0.coeff 16 =
      (-1742335801519438920177093336423298 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_17 :
    remainder3Coefficient0.coeff 17 =
      (38064345949383782936507754711195193 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_18 :
    remainder3Coefficient0.coeff 18 =
      (-179204151669257402026118359209574838 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_19 :
    remainder3Coefficient0.coeff 19 =
      (-36973979374681706412342359208334347420 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_20 :
    remainder3Coefficient0.coeff 20 =
      (2137363388566628284743357197726381838956 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_21 :
    remainder3Coefficient0.coeff 21 =
      (-71911779643193959004534831480162841168816 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_22 :
    remainder3Coefficient0.coeff 22 =
      (1762597275403315276703628289405966746342987 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_23 :
    remainder3Coefficient0.coeff 23 =
      (-34138692680849682446976950412851940339449937 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_24 :
    remainder3Coefficient0.coeff 24 =
      (552467363692672535803570517425603952564410700 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_25 :
    remainder3Coefficient0.coeff 25 =
      (-7939075987439788713884785869012474294399561470 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_26 :
    remainder3Coefficient0.coeff 26 =
      (109349853254286577338279748981779958688710271384 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_27 :
    remainder3Coefficient0.coeff 27 =
      (-1545880979781235721694231385301134279432156136508 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_28 :
    remainder3Coefficient0.coeff 28 =
      (22676504550839967189427936447813371811662024521348 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_29 :
    remainder3Coefficient0.coeff 29 =
      (-328974304001526798795544959789385551647442053342118 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_30 :
    remainder3Coefficient0.coeff 30 =
      (4465286366450333486645924557987928865749063110891113 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_31 :
    remainder3Coefficient0.coeff 31 =
      (-54858799736235509791029301212568734913907021329458784 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_32 :
    remainder3Coefficient0.coeff 32 =
      (602145153406959310447880262540369323094402427015474536 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_33 :
    remainder3Coefficient0.coeff 33 =
      (-5892564198806635769120058488175133730683428849273203299 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_34 :
    remainder3Coefficient0.coeff 34 =
      (51545635611367479734117846407920081397724562865823431419 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_35 :
    remainder3Coefficient0.coeff 35 =
      (-404733608756654388005937985259073789253768588125584448198 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_36 :
    remainder3Coefficient0.coeff 36 =
      (2864527516590043161232655711795302583444761115820971275073 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_37 :
    remainder3Coefficient0.coeff 37 =
      (-18338507132563601942380943235856576917881771753697255182725 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_38 :
    remainder3Coefficient0.coeff 38 =
      (106463557541167214228442303735616701032671133924883061691086 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_39 :
    remainder3Coefficient0.coeff 39 =
      (-561314278962909219698295422547172122011777036251181215870161 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_40 :
    remainder3Coefficient0.coeff 40 =
      (2688714399335101325596980661656839893849979702706195758065970 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_41 :
    remainder3Coefficient0.coeff 41 =
      (-11689549642467735400408356871109602940443575954274571913303935 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_42 :
    remainder3Coefficient0.coeff 42 =
      (45985306071259975175409394912470024994236286701497963142226289 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_43 :
    remainder3Coefficient0.coeff 43 =
      (-162524193462981449826461384091871109782767383312237911541949276 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_44 :
    remainder3Coefficient0.coeff 44 =
      (508227155293203124988320624447267957476766364183277258945266574 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_45 :
    remainder3Coefficient0.coeff 45 =
      (-1359566889412032846429096507235445040180812639893288373562239901 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_46 :
    remainder3Coefficient0.coeff 46 =
      (2851082208712297703151714776027122850324020555819312143829871493 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_47 :
    remainder3Coefficient0.coeff 47 =
      (-3190153207632062724964284287111805372054977741114378625081653140 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_48 :
    remainder3Coefficient0.coeff 48 =
      (-8222234960983443522939973587058089086984514578165173608118869832 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_49 :
    remainder3Coefficient0.coeff 49 =
      (71950429460641988698423177959227678104989764102893748462736114766 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_50 :
    remainder3Coefficient0.coeff 50 =
      (-318655852741105373388953630861154707199405529356719958730512207827 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_51 :
    remainder3Coefficient0.coeff 51 =
      (1138173346144201769318489239229936809648313545540220639990693475460 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_52 :
    remainder3Coefficient0.coeff 52 =
      (-3582063774549879460130271415765521782441072173836308200276279318640 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_53 :
    remainder3Coefficient0.coeff 53 =
      (9726947810203285340886442629401443956236951259119670967933377171956 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_54 :
    remainder3Coefficient0.coeff 54 =
      (-20245176225376080422475912791710571138087986505378621699306103086440 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_55 :
    remainder3Coefficient0.coeff 55 =
      (22607993508856402456617761214149894753738162723981498978965300550861 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_56 :
    remainder3Coefficient0.coeff 56 =
      (13846440143222403243857340271597973942352036638054698356320170152420 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_57 :
    remainder3Coefficient0.coeff 57 =
      (28554743406922175307074588179655867012406316324581886630530548415658 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_58 :
    remainder3Coefficient0.coeff 58 =
      (-1182651282063552015081910611553092382095478983530767711217513298572824 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_59 :
    remainder3Coefficient0.coeff 59 =
      (6187143208974982925970866126985089225146046238944149450001511003299263 : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_60 :
    remainder3Coefficient0.coeff 60 =
      -((1 * 10 ^ 70 +
        2085970620285470392865219150601545691257864750607172538217681000660039) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_61 :
    remainder3Coefficient0.coeff 61 =
      -((3 * 10 ^ 70 +
        1901383709098183409915792383015946630065796182777010317406901156610827) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_62 :
    remainder3Coefficient0.coeff 62 =
      ((30 * 10 ^ 70 +
        9561833262843952809262611815720791267176350825051048545067831418476941) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_63 :
    remainder3Coefficient0.coeff 63 =
      -((98 * 10 ^ 70 +
        7677926928852386393594783917498824380279216660370137348055931732846692) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_64 :
    remainder3Coefficient0.coeff 64 =
      ((58 * 10 ^ 70 +
        8024880259329850641699607917506419856806472613989222099654546179168908) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_65 :
    remainder3Coefficient0.coeff 65 =
      ((926 * 10 ^ 70 +
        4145145529487333065545272393485536463105174908381470661656996415373733) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_66 :
    remainder3Coefficient0.coeff 66 =
      -((4885 * 10 ^ 70 +
        4848455228927648187599058205666114899346301381293944978894488897400107) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_67 :
    remainder3Coefficient0.coeff 67 =
      ((11836 * 10 ^ 70 +
        3483970638617886026488422400632582889101072970288920770240460647017406) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_68 :
    remainder3Coefficient0.coeff 68 =
      -((1337 * 10 ^ 70 +
        0921428541403960987264206305331329502666685355146998744423451261826349) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_69 :
    remainder3Coefficient0.coeff 69 =
      -((116089 * 10 ^ 70 +
        6702235321806926155180301241708749461687596901244528567903768516672786) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_70 :
    remainder3Coefficient0.coeff 70 =
      ((541681 * 10 ^ 70 +
        9534297521735342029738650870668182171078734748142411195867178458126851) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_71 :
    remainder3Coefficient0.coeff 71 =
      -((1359845 * 10 ^ 70 +
        7153377359221241680560545494370786197657396585222808925930939766106640) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_72 :
    remainder3Coefficient0.coeff 72 =
      ((1229382 * 10 ^ 70 +
        1311286611871202468054543104929690652817501167700804438443144352646901) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_73 :
    remainder3Coefficient0.coeff 73 =
      ((6389090 * 10 ^ 70 +
        5636886912336226670298245357517314331241637596228909850780665834212548) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_74 :
    remainder3Coefficient0.coeff 74 =
      -((39604226 * 10 ^ 70 +
        2259627221364964157794682836090253498123192830176801346768031823893364) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_75 :
    remainder3Coefficient0.coeff 75 =
      ((128843926 * 10 ^ 70 +
        6026287706649311815457268670346299060155594090441456218050598517348007) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_76 :
    remainder3Coefficient0.coeff 76 =
      -((278453357 * 10 ^ 70 +
        1779230066412021845150390271391126105507858835292019039476615358329608) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B0_coeff_77 :
    remainder3Coefficient0.coeff 77 =
      ((302102269 * 10 ^ 70 +
        9295861798022802581679693657514244784648543256589748207996165763242506) : ℚ) := by
  unfold
    remainder3Coefficient0
    remainder3Coefficient0Block1
    remainder3Coefficient0Block0
    remainder3Coefficient0Chunk19
    remainder3Coefficient0Chunk18
    remainder3Coefficient0Chunk17
    remainder3Coefficient0Chunk16
    remainder3Coefficient0Chunk15
    remainder3Coefficient0Chunk14
    remainder3Coefficient0Chunk13
    remainder3Coefficient0Chunk12
    remainder3Coefficient0Chunk11
    remainder3Coefficient0Chunk10
    remainder3Coefficient0Chunk9
    remainder3Coefficient0Chunk8
    remainder3Coefficient0Chunk7
    remainder3Coefficient0Chunk6
    remainder3Coefficient0Chunk5
    remainder3Coefficient0Chunk4
    remainder3Coefficient0Chunk3
    remainder3Coefficient0Chunk2
    remainder3Coefficient0Chunk1
    remainder3Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
