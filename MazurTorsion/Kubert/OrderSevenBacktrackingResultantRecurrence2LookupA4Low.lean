/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData2
import Mathlib.Tactic.NormNum

/-!
# Recurrence 2 lookup certificate: A4 source coefficients, low half

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence2A4_coeff_0 :
    remainder2Coefficient4.coeff 0 =
      (0 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_1 :
    remainder2Coefficient4.coeff 1 =
      (-4484 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_2 :
    remainder2Coefficient4.coeff 2 =
      (1844025 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_3 :
    remainder2Coefficient4.coeff 3 =
      (3515040321 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_4 :
    remainder2Coefficient4.coeff 4 =
      (-437160397729 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_5 :
    remainder2Coefficient4.coeff 5 =
      (-30208061652185 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_6 :
    remainder2Coefficient4.coeff 6 =
      (1782788153023498 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_7 :
    remainder2Coefficient4.coeff 7 =
      (75891265047055987 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_8 :
    remainder2Coefficient4.coeff 8 =
      (-1201518328513847068 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_9 :
    remainder2Coefficient4.coeff 9 =
      (-65646022796329222704 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_10 :
    remainder2Coefficient4.coeff 10 =
      (-337144865784472729422 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_11 :
    remainder2Coefficient4.coeff 11 =
      (26993499243638401662348 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_12 :
    remainder2Coefficient4.coeff 12 =
      (200113653847991665364200 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_13 :
    remainder2Coefficient4.coeff 13 =
      (-1731033120215705441743047 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_14 :
    remainder2Coefficient4.coeff 14 =
      (-87249910341251524126232233 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_15 :
    remainder2Coefficient4.coeff 15 =
      (245658066250066217208463354 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_16 :
    remainder2Coefficient4.coeff 16 =
      (6122558870452026951957834792 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_17 :
    remainder2Coefficient4.coeff 17 =
      (54895998869065053760926250741 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_18 :
    remainder2Coefficient4.coeff 18 =
      (-761593636281390880971590410869 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_19 :
    remainder2Coefficient4.coeff 19 =
      (-3481706658519367446286379590379 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_20 :
    remainder2Coefficient4.coeff 20 =
      (21083279719613282317534843566219 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_21 :
    remainder2Coefficient4.coeff 21 =
      (366155791030503869533800181563968 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_22 :
    remainder2Coefficient4.coeff 22 =
      (-995548660916269458131140851756424 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_23 :
    remainder2Coefficient4.coeff 23 =
      (-15850906589950836393883262015590003 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_24 :
    remainder2Coefficient4.coeff 24 =
      (11305178887891113532147551672536495 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_25 :
    remainder2Coefficient4.coeff 25 =
      (653378206831544942846275668563282656 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_26 :
    remainder2Coefficient4.coeff 26 =
      (-128962834558277521146661286351655984 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_27 :
    remainder2Coefficient4.coeff 27 =
      (-19964503768396229430711371608755978186 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_28 :
    remainder2Coefficient4.coeff 28 =
      (-919451315218442547947728140666856922 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_29 :
    remainder2Coefficient4.coeff 29 =
      (526180748310193457410819886811775418595 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_30 :
    remainder2Coefficient4.coeff 30 =
      (-117040313349008727634316589506249842791 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_31 :
    remainder2Coefficient4.coeff 31 =
      (-11573839367349732358281411554026148918924 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_32 :
    remainder2Coefficient4.coeff 32 =
      (9159932449270445531476273128321321702802 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_33 :
    remainder2Coefficient4.coeff 33 =
      (212028110350396528738533651857411112191845 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_34 :
    remainder2Coefficient4.coeff 34 =
      (-348412100404979138215482684611103879238099 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_35 :
    remainder2Coefficient4.coeff 35 =
      (-3089012035874903642467874332463622276635518 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_36 :
    remainder2Coefficient4.coeff 36 =
      (8787953787800057138534507392612999025079156 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_37 :
    remainder2Coefficient4.coeff 37 =
      (32298868767447754344864573417396398055540391 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_38 :
    remainder2Coefficient4.coeff 38 =
      (-158956189353983597640140225968330405329202570 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_39 :
    remainder2Coefficient4.coeff 39 =
      (-159946346627034111492081833052243935085826347 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_40 :
    remainder2Coefficient4.coeff 40 =
      (2053117137312446097252905665708171293294955350 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_41 :
    remainder2Coefficient4.coeff 41 =
      (-1692827534970199296655865543170820237029316689 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_42 :
    remainder2Coefficient4.coeff 42 =
      (-17328442228565544484785993690729563650850253531 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_43 :
    remainder2Coefficient4.coeff 43 =
      (46882454155572735710251684103067266472037240530 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_44 :
    remainder2Coefficient4.coeff 44 =
      (60699672912375196361252975647329068625681778521 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_45 :
    remainder2Coefficient4.coeff 45 =
      (-492964048180503567794237322887238239808056091730 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_46 :
    remainder2Coefficient4.coeff 46 =
      (535034283561283993430861041226970857196747060306 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_47 :
    remainder2Coefficient4.coeff 47 =
      (2318639987710616732879835244395478339063614734231 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_48 :
    remainder2Coefficient4.coeff 48 =
      (-8340536903252677298548724493654868460098424907864 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_49 :
    remainder2Coefficient4.coeff 49 =
      (4076918239957814399829082024624735469727184086254 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_50 :
    remainder2Coefficient4.coeff 50 =
      (37356252392369544133903144701282118686545444589085 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_51 :
    remainder2Coefficient4.coeff 51 =
      (-104159695137006962784475162704718105817439999544319 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
