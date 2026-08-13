/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData2
import Mathlib.Tactic.NormNum

/-!
# Recurrence 2 lookup certificate: A2 source coefficients, low half

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence2A2_coeff_0 :
    remainder2Coefficient2.coeff 0 =
      (0 : ℚ) := by
  unfold
    remainder2Coefficient2
    remainder2Coefficient2Block1
    remainder2Coefficient2Block0
    remainder2Coefficient2Chunk13
    remainder2Coefficient2Chunk12
    remainder2Coefficient2Chunk11
    remainder2Coefficient2Chunk10
    remainder2Coefficient2Chunk9
    remainder2Coefficient2Chunk8
    remainder2Coefficient2Chunk7
    remainder2Coefficient2Chunk6
    remainder2Coefficient2Chunk5
    remainder2Coefficient2Chunk4
    remainder2Coefficient2Chunk3
    remainder2Coefficient2Chunk2
    remainder2Coefficient2Chunk1
    remainder2Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A2_coeff_1 :
    remainder2Coefficient2.coeff 1 =
      (0 : ℚ) := by
  unfold
    remainder2Coefficient2
    remainder2Coefficient2Block1
    remainder2Coefficient2Block0
    remainder2Coefficient2Chunk13
    remainder2Coefficient2Chunk12
    remainder2Coefficient2Chunk11
    remainder2Coefficient2Chunk10
    remainder2Coefficient2Chunk9
    remainder2Coefficient2Chunk8
    remainder2Coefficient2Chunk7
    remainder2Coefficient2Chunk6
    remainder2Coefficient2Chunk5
    remainder2Coefficient2Chunk4
    remainder2Coefficient2Chunk3
    remainder2Coefficient2Chunk2
    remainder2Coefficient2Chunk1
    remainder2Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A2_coeff_2 :
    remainder2Coefficient2.coeff 2 =
      (-4313 : ℚ) := by
  unfold
    remainder2Coefficient2
    remainder2Coefficient2Block1
    remainder2Coefficient2Block0
    remainder2Coefficient2Chunk13
    remainder2Coefficient2Chunk12
    remainder2Coefficient2Chunk11
    remainder2Coefficient2Chunk10
    remainder2Coefficient2Chunk9
    remainder2Coefficient2Chunk8
    remainder2Coefficient2Chunk7
    remainder2Coefficient2Chunk6
    remainder2Coefficient2Chunk5
    remainder2Coefficient2Chunk4
    remainder2Coefficient2Chunk3
    remainder2Coefficient2Chunk2
    remainder2Coefficient2Chunk1
    remainder2Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A2_coeff_3 :
    remainder2Coefficient2.coeff 3 =
      (18508415 : ℚ) := by
  unfold
    remainder2Coefficient2
    remainder2Coefficient2Block1
    remainder2Coefficient2Block0
    remainder2Coefficient2Chunk13
    remainder2Coefficient2Chunk12
    remainder2Coefficient2Chunk11
    remainder2Coefficient2Chunk10
    remainder2Coefficient2Chunk9
    remainder2Coefficient2Chunk8
    remainder2Coefficient2Chunk7
    remainder2Coefficient2Chunk6
    remainder2Coefficient2Chunk5
    remainder2Coefficient2Chunk4
    remainder2Coefficient2Chunk3
    remainder2Coefficient2Chunk2
    remainder2Coefficient2Chunk1
    remainder2Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A2_coeff_4 :
    remainder2Coefficient2.coeff 4 =
      (-1179368522 : ℚ) := by
  unfold
    remainder2Coefficient2
    remainder2Coefficient2Block1
    remainder2Coefficient2Block0
    remainder2Coefficient2Chunk13
    remainder2Coefficient2Chunk12
    remainder2Coefficient2Chunk11
    remainder2Coefficient2Chunk10
    remainder2Coefficient2Chunk9
    remainder2Coefficient2Chunk8
    remainder2Coefficient2Chunk7
    remainder2Coefficient2Chunk6
    remainder2Coefficient2Chunk5
    remainder2Coefficient2Chunk4
    remainder2Coefficient2Chunk3
    remainder2Coefficient2Chunk2
    remainder2Coefficient2Chunk1
    remainder2Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A2_coeff_5 :
    remainder2Coefficient2.coeff 5 =
      (-726119201869 : ℚ) := by
  unfold
    remainder2Coefficient2
    remainder2Coefficient2Block1
    remainder2Coefficient2Block0
    remainder2Coefficient2Chunk13
    remainder2Coefficient2Chunk12
    remainder2Coefficient2Chunk11
    remainder2Coefficient2Chunk10
    remainder2Coefficient2Chunk9
    remainder2Coefficient2Chunk8
    remainder2Coefficient2Chunk7
    remainder2Coefficient2Chunk6
    remainder2Coefficient2Chunk5
    remainder2Coefficient2Chunk4
    remainder2Coefficient2Chunk3
    remainder2Coefficient2Chunk2
    remainder2Coefficient2Chunk1
    remainder2Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A2_coeff_6 :
    remainder2Coefficient2.coeff 6 =
      (64443948614929 : ℚ) := by
  unfold
    remainder2Coefficient2
    remainder2Coefficient2Block1
    remainder2Coefficient2Block0
    remainder2Coefficient2Chunk13
    remainder2Coefficient2Chunk12
    remainder2Coefficient2Chunk11
    remainder2Coefficient2Chunk10
    remainder2Coefficient2Chunk9
    remainder2Coefficient2Chunk8
    remainder2Coefficient2Chunk7
    remainder2Coefficient2Chunk6
    remainder2Coefficient2Chunk5
    remainder2Coefficient2Chunk4
    remainder2Coefficient2Chunk3
    remainder2Coefficient2Chunk2
    remainder2Coefficient2Chunk1
    remainder2Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A2_coeff_7 :
    remainder2Coefficient2.coeff 7 =
      (-1634796781931808 : ℚ) := by
  unfold
    remainder2Coefficient2
    remainder2Coefficient2Block1
    remainder2Coefficient2Block0
    remainder2Coefficient2Chunk13
    remainder2Coefficient2Chunk12
    remainder2Coefficient2Chunk11
    remainder2Coefficient2Chunk10
    remainder2Coefficient2Chunk9
    remainder2Coefficient2Chunk8
    remainder2Coefficient2Chunk7
    remainder2Coefficient2Chunk6
    remainder2Coefficient2Chunk5
    remainder2Coefficient2Chunk4
    remainder2Coefficient2Chunk3
    remainder2Coefficient2Chunk2
    remainder2Coefficient2Chunk1
    remainder2Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A2_coeff_8 :
    remainder2Coefficient2.coeff 8 =
      (-53104121001510770 : ℚ) := by
  unfold
    remainder2Coefficient2
    remainder2Coefficient2Block1
    remainder2Coefficient2Block0
    remainder2Coefficient2Chunk13
    remainder2Coefficient2Chunk12
    remainder2Coefficient2Chunk11
    remainder2Coefficient2Chunk10
    remainder2Coefficient2Chunk9
    remainder2Coefficient2Chunk8
    remainder2Coefficient2Chunk7
    remainder2Coefficient2Chunk6
    remainder2Coefficient2Chunk5
    remainder2Coefficient2Chunk4
    remainder2Coefficient2Chunk3
    remainder2Coefficient2Chunk2
    remainder2Coefficient2Chunk1
    remainder2Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A2_coeff_9 :
    remainder2Coefficient2.coeff 9 =
      (4429251272553627031 : ℚ) := by
  unfold
    remainder2Coefficient2
    remainder2Coefficient2Block1
    remainder2Coefficient2Block0
    remainder2Coefficient2Chunk13
    remainder2Coefficient2Chunk12
    remainder2Coefficient2Chunk11
    remainder2Coefficient2Chunk10
    remainder2Coefficient2Chunk9
    remainder2Coefficient2Chunk8
    remainder2Coefficient2Chunk7
    remainder2Coefficient2Chunk6
    remainder2Coefficient2Chunk5
    remainder2Coefficient2Chunk4
    remainder2Coefficient2Chunk3
    remainder2Coefficient2Chunk2
    remainder2Coefficient2Chunk1
    remainder2Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A2_coeff_10 :
    remainder2Coefficient2.coeff 10 =
      (44894677717832501843 : ℚ) := by
  unfold
    remainder2Coefficient2
    remainder2Coefficient2Block1
    remainder2Coefficient2Block0
    remainder2Coefficient2Chunk13
    remainder2Coefficient2Chunk12
    remainder2Coefficient2Chunk11
    remainder2Coefficient2Chunk10
    remainder2Coefficient2Chunk9
    remainder2Coefficient2Chunk8
    remainder2Coefficient2Chunk7
    remainder2Coefficient2Chunk6
    remainder2Coefficient2Chunk5
    remainder2Coefficient2Chunk4
    remainder2Coefficient2Chunk3
    remainder2Coefficient2Chunk2
    remainder2Coefficient2Chunk1
    remainder2Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A2_coeff_11 :
    remainder2Coefficient2.coeff 11 =
      (-3305729713116580021438 : ℚ) := by
  unfold
    remainder2Coefficient2
    remainder2Coefficient2Block1
    remainder2Coefficient2Block0
    remainder2Coefficient2Chunk13
    remainder2Coefficient2Chunk12
    remainder2Coefficient2Chunk11
    remainder2Coefficient2Chunk10
    remainder2Coefficient2Chunk9
    remainder2Coefficient2Chunk8
    remainder2Coefficient2Chunk7
    remainder2Coefficient2Chunk6
    remainder2Coefficient2Chunk5
    remainder2Coefficient2Chunk4
    remainder2Coefficient2Chunk3
    remainder2Coefficient2Chunk2
    remainder2Coefficient2Chunk1
    remainder2Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A2_coeff_12 :
    remainder2Coefficient2.coeff 12 =
      (-44370403879186022184327 : ℚ) := by
  unfold
    remainder2Coefficient2
    remainder2Coefficient2Block1
    remainder2Coefficient2Block0
    remainder2Coefficient2Chunk13
    remainder2Coefficient2Chunk12
    remainder2Coefficient2Chunk11
    remainder2Coefficient2Chunk10
    remainder2Coefficient2Chunk9
    remainder2Coefficient2Chunk8
    remainder2Coefficient2Chunk7
    remainder2Coefficient2Chunk6
    remainder2Coefficient2Chunk5
    remainder2Coefficient2Chunk4
    remainder2Coefficient2Chunk3
    remainder2Coefficient2Chunk2
    remainder2Coefficient2Chunk1
    remainder2Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A2_coeff_13 :
    remainder2Coefficient2.coeff 13 =
      (1038308847642591349427606 : ℚ) := by
  unfold
    remainder2Coefficient2
    remainder2Coefficient2Block1
    remainder2Coefficient2Block0
    remainder2Coefficient2Chunk13
    remainder2Coefficient2Chunk12
    remainder2Coefficient2Chunk11
    remainder2Coefficient2Chunk10
    remainder2Coefficient2Chunk9
    remainder2Coefficient2Chunk8
    remainder2Coefficient2Chunk7
    remainder2Coefficient2Chunk6
    remainder2Coefficient2Chunk5
    remainder2Coefficient2Chunk4
    remainder2Coefficient2Chunk3
    remainder2Coefficient2Chunk2
    remainder2Coefficient2Chunk1
    remainder2Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A2_coeff_14 :
    remainder2Coefficient2.coeff 14 =
      (15998025457352783001220174 : ℚ) := by
  unfold
    remainder2Coefficient2
    remainder2Coefficient2Block1
    remainder2Coefficient2Block0
    remainder2Coefficient2Chunk13
    remainder2Coefficient2Chunk12
    remainder2Coefficient2Chunk11
    remainder2Coefficient2Chunk10
    remainder2Coefficient2Chunk9
    remainder2Coefficient2Chunk8
    remainder2Coefficient2Chunk7
    remainder2Coefficient2Chunk6
    remainder2Coefficient2Chunk5
    remainder2Coefficient2Chunk4
    remainder2Coefficient2Chunk3
    remainder2Coefficient2Chunk2
    remainder2Coefficient2Chunk1
    remainder2Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A2_coeff_15 :
    remainder2Coefficient2.coeff 15 =
      (-100565161540304756843088699 : ℚ) := by
  unfold
    remainder2Coefficient2
    remainder2Coefficient2Block1
    remainder2Coefficient2Block0
    remainder2Coefficient2Chunk13
    remainder2Coefficient2Chunk12
    remainder2Coefficient2Chunk11
    remainder2Coefficient2Chunk10
    remainder2Coefficient2Chunk9
    remainder2Coefficient2Chunk8
    remainder2Coefficient2Chunk7
    remainder2Coefficient2Chunk6
    remainder2Coefficient2Chunk5
    remainder2Coefficient2Chunk4
    remainder2Coefficient2Chunk3
    remainder2Coefficient2Chunk2
    remainder2Coefficient2Chunk1
    remainder2Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A2_coeff_16 :
    remainder2Coefficient2.coeff 16 =
      (-3838383077263422427097601024 : ℚ) := by
  unfold
    remainder2Coefficient2
    remainder2Coefficient2Block1
    remainder2Coefficient2Block0
    remainder2Coefficient2Chunk13
    remainder2Coefficient2Chunk12
    remainder2Coefficient2Chunk11
    remainder2Coefficient2Chunk10
    remainder2Coefficient2Chunk9
    remainder2Coefficient2Chunk8
    remainder2Coefficient2Chunk7
    remainder2Coefficient2Chunk6
    remainder2Coefficient2Chunk5
    remainder2Coefficient2Chunk4
    remainder2Coefficient2Chunk3
    remainder2Coefficient2Chunk2
    remainder2Coefficient2Chunk1
    remainder2Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A2_coeff_17 :
    remainder2Coefficient2.coeff 17 =
      (10609409481487786287893449330 : ℚ) := by
  unfold
    remainder2Coefficient2
    remainder2Coefficient2Block1
    remainder2Coefficient2Block0
    remainder2Coefficient2Chunk13
    remainder2Coefficient2Chunk12
    remainder2Coefficient2Chunk11
    remainder2Coefficient2Chunk10
    remainder2Coefficient2Chunk9
    remainder2Coefficient2Chunk8
    remainder2Coefficient2Chunk7
    remainder2Coefficient2Chunk6
    remainder2Coefficient2Chunk5
    remainder2Coefficient2Chunk4
    remainder2Coefficient2Chunk3
    remainder2Coefficient2Chunk2
    remainder2Coefficient2Chunk1
    remainder2Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A2_coeff_18 :
    remainder2Coefficient2.coeff 18 =
      (357912551995618314750281664824 : ℚ) := by
  unfold
    remainder2Coefficient2
    remainder2Coefficient2Block1
    remainder2Coefficient2Block0
    remainder2Coefficient2Chunk13
    remainder2Coefficient2Chunk12
    remainder2Coefficient2Chunk11
    remainder2Coefficient2Chunk10
    remainder2Coefficient2Chunk9
    remainder2Coefficient2Chunk8
    remainder2Coefficient2Chunk7
    remainder2Coefficient2Chunk6
    remainder2Coefficient2Chunk5
    remainder2Coefficient2Chunk4
    remainder2Coefficient2Chunk3
    remainder2Coefficient2Chunk2
    remainder2Coefficient2Chunk1
    remainder2Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A2_coeff_19 :
    remainder2Coefficient2.coeff 19 =
      (928321599646397579187788779389 : ℚ) := by
  unfold
    remainder2Coefficient2
    remainder2Coefficient2Block1
    remainder2Coefficient2Block0
    remainder2Coefficient2Chunk13
    remainder2Coefficient2Chunk12
    remainder2Coefficient2Chunk11
    remainder2Coefficient2Chunk10
    remainder2Coefficient2Chunk9
    remainder2Coefficient2Chunk8
    remainder2Coefficient2Chunk7
    remainder2Coefficient2Chunk6
    remainder2Coefficient2Chunk5
    remainder2Coefficient2Chunk4
    remainder2Coefficient2Chunk3
    remainder2Coefficient2Chunk2
    remainder2Coefficient2Chunk1
    remainder2Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A2_coeff_20 :
    remainder2Coefficient2.coeff 20 =
      (-39010431621283220839231554468746 : ℚ) := by
  unfold
    remainder2Coefficient2
    remainder2Coefficient2Block1
    remainder2Coefficient2Block0
    remainder2Coefficient2Chunk13
    remainder2Coefficient2Chunk12
    remainder2Coefficient2Chunk11
    remainder2Coefficient2Chunk10
    remainder2Coefficient2Chunk9
    remainder2Coefficient2Chunk8
    remainder2Coefficient2Chunk7
    remainder2Coefficient2Chunk6
    remainder2Coefficient2Chunk5
    remainder2Coefficient2Chunk4
    remainder2Coefficient2Chunk3
    remainder2Coefficient2Chunk2
    remainder2Coefficient2Chunk1
    remainder2Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A2_coeff_21 :
    remainder2Coefficient2.coeff 21 =
      (-44113655110558033415564496971977 : ℚ) := by
  unfold
    remainder2Coefficient2
    remainder2Coefficient2Block1
    remainder2Coefficient2Block0
    remainder2Coefficient2Chunk13
    remainder2Coefficient2Chunk12
    remainder2Coefficient2Chunk11
    remainder2Coefficient2Chunk10
    remainder2Coefficient2Chunk9
    remainder2Coefficient2Chunk8
    remainder2Coefficient2Chunk7
    remainder2Coefficient2Chunk6
    remainder2Coefficient2Chunk5
    remainder2Coefficient2Chunk4
    remainder2Coefficient2Chunk3
    remainder2Coefficient2Chunk2
    remainder2Coefficient2Chunk1
    remainder2Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A2_coeff_22 :
    remainder2Coefficient2.coeff 22 =
      (1998385302311546909527456011604480 : ℚ) := by
  unfold
    remainder2Coefficient2
    remainder2Coefficient2Block1
    remainder2Coefficient2Block0
    remainder2Coefficient2Chunk13
    remainder2Coefficient2Chunk12
    remainder2Coefficient2Chunk11
    remainder2Coefficient2Chunk10
    remainder2Coefficient2Chunk9
    remainder2Coefficient2Chunk8
    remainder2Coefficient2Chunk7
    remainder2Coefficient2Chunk6
    remainder2Coefficient2Chunk5
    remainder2Coefficient2Chunk4
    remainder2Coefficient2Chunk3
    remainder2Coefficient2Chunk2
    remainder2Coefficient2Chunk1
    remainder2Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A2_coeff_23 :
    remainder2Coefficient2.coeff 23 =
      (7168047773872259887036010762730379 : ℚ) := by
  unfold
    remainder2Coefficient2
    remainder2Coefficient2Block1
    remainder2Coefficient2Block0
    remainder2Coefficient2Chunk13
    remainder2Coefficient2Chunk12
    remainder2Coefficient2Chunk11
    remainder2Coefficient2Chunk10
    remainder2Coefficient2Chunk9
    remainder2Coefficient2Chunk8
    remainder2Coefficient2Chunk7
    remainder2Coefficient2Chunk6
    remainder2Coefficient2Chunk5
    remainder2Coefficient2Chunk4
    remainder2Coefficient2Chunk3
    remainder2Coefficient2Chunk2
    remainder2Coefficient2Chunk1
    remainder2Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A2_coeff_24 :
    remainder2Coefficient2.coeff 24 =
      (-120219085005287976859016785080841404 : ℚ) := by
  unfold
    remainder2Coefficient2
    remainder2Coefficient2Block1
    remainder2Coefficient2Block0
    remainder2Coefficient2Chunk13
    remainder2Coefficient2Chunk12
    remainder2Coefficient2Chunk11
    remainder2Coefficient2Chunk10
    remainder2Coefficient2Chunk9
    remainder2Coefficient2Chunk8
    remainder2Coefficient2Chunk7
    remainder2Coefficient2Chunk6
    remainder2Coefficient2Chunk5
    remainder2Coefficient2Chunk4
    remainder2Coefficient2Chunk3
    remainder2Coefficient2Chunk2
    remainder2Coefficient2Chunk1
    remainder2Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A2_coeff_25 :
    remainder2Coefficient2.coeff 25 =
      (-272065361572137179529501208609249331 : ℚ) := by
  unfold
    remainder2Coefficient2
    remainder2Coefficient2Block1
    remainder2Coefficient2Block0
    remainder2Coefficient2Chunk13
    remainder2Coefficient2Chunk12
    remainder2Coefficient2Chunk11
    remainder2Coefficient2Chunk10
    remainder2Coefficient2Chunk9
    remainder2Coefficient2Chunk8
    remainder2Coefficient2Chunk7
    remainder2Coefficient2Chunk6
    remainder2Coefficient2Chunk5
    remainder2Coefficient2Chunk4
    remainder2Coefficient2Chunk3
    remainder2Coefficient2Chunk2
    remainder2Coefficient2Chunk1
    remainder2Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A2_coeff_26 :
    remainder2Coefficient2.coeff 26 =
      (4809921067274839057864714570624963506 : ℚ) := by
  unfold
    remainder2Coefficient2
    remainder2Coefficient2Block1
    remainder2Coefficient2Block0
    remainder2Coefficient2Chunk13
    remainder2Coefficient2Chunk12
    remainder2Coefficient2Chunk11
    remainder2Coefficient2Chunk10
    remainder2Coefficient2Chunk9
    remainder2Coefficient2Chunk8
    remainder2Coefficient2Chunk7
    remainder2Coefficient2Chunk6
    remainder2Coefficient2Chunk5
    remainder2Coefficient2Chunk4
    remainder2Coefficient2Chunk3
    remainder2Coefficient2Chunk2
    remainder2Coefficient2Chunk1
    remainder2Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A2_coeff_27 :
    remainder2Coefficient2.coeff 27 =
      (10977775776437172250288677711940278903 : ℚ) := by
  unfold
    remainder2Coefficient2
    remainder2Coefficient2Block1
    remainder2Coefficient2Block0
    remainder2Coefficient2Chunk13
    remainder2Coefficient2Chunk12
    remainder2Coefficient2Chunk11
    remainder2Coefficient2Chunk10
    remainder2Coefficient2Chunk9
    remainder2Coefficient2Chunk8
    remainder2Coefficient2Chunk7
    remainder2Coefficient2Chunk6
    remainder2Coefficient2Chunk5
    remainder2Coefficient2Chunk4
    remainder2Coefficient2Chunk3
    remainder2Coefficient2Chunk2
    remainder2Coefficient2Chunk1
    remainder2Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A2_coeff_28 :
    remainder2Coefficient2.coeff 28 =
      (-182892475529011048951487063637634553314 : ℚ) := by
  unfold
    remainder2Coefficient2
    remainder2Coefficient2Block1
    remainder2Coefficient2Block0
    remainder2Coefficient2Chunk13
    remainder2Coefficient2Chunk12
    remainder2Coefficient2Chunk11
    remainder2Coefficient2Chunk10
    remainder2Coefficient2Chunk9
    remainder2Coefficient2Chunk8
    remainder2Coefficient2Chunk7
    remainder2Coefficient2Chunk6
    remainder2Coefficient2Chunk5
    remainder2Coefficient2Chunk4
    remainder2Coefficient2Chunk3
    remainder2Coefficient2Chunk2
    remainder2Coefficient2Chunk1
    remainder2Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A2_coeff_29 :
    remainder2Coefficient2.coeff 29 =
      (-225651086921399577429239301721385471573 : ℚ) := by
  unfold
    remainder2Coefficient2
    remainder2Coefficient2Block1
    remainder2Coefficient2Block0
    remainder2Coefficient2Chunk13
    remainder2Coefficient2Chunk12
    remainder2Coefficient2Chunk11
    remainder2Coefficient2Chunk10
    remainder2Coefficient2Chunk9
    remainder2Coefficient2Chunk8
    remainder2Coefficient2Chunk7
    remainder2Coefficient2Chunk6
    remainder2Coefficient2Chunk5
    remainder2Coefficient2Chunk4
    remainder2Coefficient2Chunk3
    remainder2Coefficient2Chunk2
    remainder2Coefficient2Chunk1
    remainder2Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A2_coeff_30 :
    remainder2Coefficient2.coeff 30 =
      (5594738952022077263553172674468414526285 : ℚ) := by
  unfold
    remainder2Coefficient2
    remainder2Coefficient2Block1
    remainder2Coefficient2Block0
    remainder2Coefficient2Chunk13
    remainder2Coefficient2Chunk12
    remainder2Coefficient2Chunk11
    remainder2Coefficient2Chunk10
    remainder2Coefficient2Chunk9
    remainder2Coefficient2Chunk8
    remainder2Coefficient2Chunk7
    remainder2Coefficient2Chunk6
    remainder2Coefficient2Chunk5
    remainder2Coefficient2Chunk4
    remainder2Coefficient2Chunk3
    remainder2Coefficient2Chunk2
    remainder2Coefficient2Chunk1
    remainder2Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A2_coeff_31 :
    remainder2Coefficient2.coeff 31 =
      (1277630644490436651545302781724918563567 : ℚ) := by
  unfold
    remainder2Coefficient2
    remainder2Coefficient2Block1
    remainder2Coefficient2Block0
    remainder2Coefficient2Chunk13
    remainder2Coefficient2Chunk12
    remainder2Coefficient2Chunk11
    remainder2Coefficient2Chunk10
    remainder2Coefficient2Chunk9
    remainder2Coefficient2Chunk8
    remainder2Coefficient2Chunk7
    remainder2Coefficient2Chunk6
    remainder2Coefficient2Chunk5
    remainder2Coefficient2Chunk4
    remainder2Coefficient2Chunk3
    remainder2Coefficient2Chunk2
    remainder2Coefficient2Chunk1
    remainder2Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A2_coeff_32 :
    remainder2Coefficient2.coeff 32 =
      (-143971490148075201103356211213635554595906 : ℚ) := by
  unfold
    remainder2Coefficient2
    remainder2Coefficient2Block1
    remainder2Coefficient2Block0
    remainder2Coefficient2Chunk13
    remainder2Coefficient2Chunk12
    remainder2Coefficient2Chunk11
    remainder2Coefficient2Chunk10
    remainder2Coefficient2Chunk9
    remainder2Coefficient2Chunk8
    remainder2Coefficient2Chunk7
    remainder2Coefficient2Chunk6
    remainder2Coefficient2Chunk5
    remainder2Coefficient2Chunk4
    remainder2Coefficient2Chunk3
    remainder2Coefficient2Chunk2
    remainder2Coefficient2Chunk1
    remainder2Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A2_coeff_33 :
    remainder2Coefficient2.coeff 33 =
      (141516256736775030680012138512082832312497 : ℚ) := by
  unfold
    remainder2Coefficient2
    remainder2Coefficient2Block1
    remainder2Coefficient2Block0
    remainder2Coefficient2Chunk13
    remainder2Coefficient2Chunk12
    remainder2Coefficient2Chunk11
    remainder2Coefficient2Chunk10
    remainder2Coefficient2Chunk9
    remainder2Coefficient2Chunk8
    remainder2Coefficient2Chunk7
    remainder2Coefficient2Chunk6
    remainder2Coefficient2Chunk5
    remainder2Coefficient2Chunk4
    remainder2Coefficient2Chunk3
    remainder2Coefficient2Chunk2
    remainder2Coefficient2Chunk1
    remainder2Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A2_coeff_34 :
    remainder2Coefficient2.coeff 34 =
      (2934737362609721978989121199535211802940135 : ℚ) := by
  unfold
    remainder2Coefficient2
    remainder2Coefficient2Block1
    remainder2Coefficient2Block0
    remainder2Coefficient2Chunk13
    remainder2Coefficient2Chunk12
    remainder2Coefficient2Chunk11
    remainder2Coefficient2Chunk10
    remainder2Coefficient2Chunk9
    remainder2Coefficient2Chunk8
    remainder2Coefficient2Chunk7
    remainder2Coefficient2Chunk6
    remainder2Coefficient2Chunk5
    remainder2Coefficient2Chunk4
    remainder2Coefficient2Chunk3
    remainder2Coefficient2Chunk2
    remainder2Coefficient2Chunk1
    remainder2Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A2_coeff_35 :
    remainder2Coefficient2.coeff 35 =
      (-6992542448096665025565927640957960661978556 : ℚ) := by
  unfold
    remainder2Coefficient2
    remainder2Coefficient2Block1
    remainder2Coefficient2Block0
    remainder2Coefficient2Chunk13
    remainder2Coefficient2Chunk12
    remainder2Coefficient2Chunk11
    remainder2Coefficient2Chunk10
    remainder2Coefficient2Chunk9
    remainder2Coefficient2Chunk8
    remainder2Coefficient2Chunk7
    remainder2Coefficient2Chunk6
    remainder2Coefficient2Chunk5
    remainder2Coefficient2Chunk4
    remainder2Coefficient2Chunk3
    remainder2Coefficient2Chunk2
    remainder2Coefficient2Chunk1
    remainder2Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A2_coeff_36 :
    remainder2Coefficient2.coeff 36 =
      (-44072802935403696670155203768536842732121167 : ℚ) := by
  unfold
    remainder2Coefficient2
    remainder2Coefficient2Block1
    remainder2Coefficient2Block0
    remainder2Coefficient2Chunk13
    remainder2Coefficient2Chunk12
    remainder2Coefficient2Chunk11
    remainder2Coefficient2Chunk10
    remainder2Coefficient2Chunk9
    remainder2Coefficient2Chunk8
    remainder2Coefficient2Chunk7
    remainder2Coefficient2Chunk6
    remainder2Coefficient2Chunk5
    remainder2Coefficient2Chunk4
    remainder2Coefficient2Chunk3
    remainder2Coefficient2Chunk2
    remainder2Coefficient2Chunk1
    remainder2Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A2_coeff_37 :
    remainder2Coefficient2.coeff 37 =
      (192741970197878757144563539088813369313968168 : ℚ) := by
  unfold
    remainder2Coefficient2
    remainder2Coefficient2Block1
    remainder2Coefficient2Block0
    remainder2Coefficient2Chunk13
    remainder2Coefficient2Chunk12
    remainder2Coefficient2Chunk11
    remainder2Coefficient2Chunk10
    remainder2Coefficient2Chunk9
    remainder2Coefficient2Chunk8
    remainder2Coefficient2Chunk7
    remainder2Coefficient2Chunk6
    remainder2Coefficient2Chunk5
    remainder2Coefficient2Chunk4
    remainder2Coefficient2Chunk3
    remainder2Coefficient2Chunk2
    remainder2Coefficient2Chunk1
    remainder2Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A2_coeff_38 :
    remainder2Coefficient2.coeff 38 =
      (378998640258419723632070884120051362325277745 : ℚ) := by
  unfold
    remainder2Coefficient2
    remainder2Coefficient2Block1
    remainder2Coefficient2Block0
    remainder2Coefficient2Chunk13
    remainder2Coefficient2Chunk12
    remainder2Coefficient2Chunk11
    remainder2Coefficient2Chunk10
    remainder2Coefficient2Chunk9
    remainder2Coefficient2Chunk8
    remainder2Coefficient2Chunk7
    remainder2Coefficient2Chunk6
    remainder2Coefficient2Chunk5
    remainder2Coefficient2Chunk4
    remainder2Coefficient2Chunk3
    remainder2Coefficient2Chunk2
    remainder2Coefficient2Chunk1
    remainder2Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A2_coeff_39 :
    remainder2Coefficient2.coeff 39 =
      (-3579749608066737552394659611752271346887827974 : ℚ) := by
  unfold
    remainder2Coefficient2
    remainder2Coefficient2Block1
    remainder2Coefficient2Block0
    remainder2Coefficient2Chunk13
    remainder2Coefficient2Chunk12
    remainder2Coefficient2Chunk11
    remainder2Coefficient2Chunk10
    remainder2Coefficient2Chunk9
    remainder2Coefficient2Chunk8
    remainder2Coefficient2Chunk7
    remainder2Coefficient2Chunk6
    remainder2Coefficient2Chunk5
    remainder2Coefficient2Chunk4
    remainder2Coefficient2Chunk3
    remainder2Coefficient2Chunk2
    remainder2Coefficient2Chunk1
    remainder2Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A2_coeff_40 :
    remainder2Coefficient2.coeff 40 =
      (1470706088616565346583942807448141460401188945 : ℚ) := by
  unfold
    remainder2Coefficient2
    remainder2Coefficient2Block1
    remainder2Coefficient2Block0
    remainder2Coefficient2Chunk13
    remainder2Coefficient2Chunk12
    remainder2Coefficient2Chunk11
    remainder2Coefficient2Chunk10
    remainder2Coefficient2Chunk9
    remainder2Coefficient2Chunk8
    remainder2Coefficient2Chunk7
    remainder2Coefficient2Chunk6
    remainder2Coefficient2Chunk5
    remainder2Coefficient2Chunk4
    remainder2Coefficient2Chunk3
    remainder2Coefficient2Chunk2
    remainder2Coefficient2Chunk1
    remainder2Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A2_coeff_41 :
    remainder2Coefficient2.coeff 41 =
      (43883561445677244621270552241179903867916776540 : ℚ) := by
  unfold
    remainder2Coefficient2
    remainder2Coefficient2Block1
    remainder2Coefficient2Block0
    remainder2Coefficient2Chunk13
    remainder2Coefficient2Chunk12
    remainder2Coefficient2Chunk11
    remainder2Coefficient2Chunk10
    remainder2Coefficient2Chunk9
    remainder2Coefficient2Chunk8
    remainder2Coefficient2Chunk7
    remainder2Coefficient2Chunk6
    remainder2Coefficient2Chunk5
    remainder2Coefficient2Chunk4
    remainder2Coefficient2Chunk3
    remainder2Coefficient2Chunk2
    remainder2Coefficient2Chunk1
    remainder2Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A2_coeff_42 :
    remainder2Coefficient2.coeff 42 =
      (-107804191716905270671379301045017348646752444777 : ℚ) := by
  unfold
    remainder2Coefficient2
    remainder2Coefficient2Block1
    remainder2Coefficient2Block0
    remainder2Coefficient2Chunk13
    remainder2Coefficient2Chunk12
    remainder2Coefficient2Chunk11
    remainder2Coefficient2Chunk10
    remainder2Coefficient2Chunk9
    remainder2Coefficient2Chunk8
    remainder2Coefficient2Chunk7
    remainder2Coefficient2Chunk6
    remainder2Coefficient2Chunk5
    remainder2Coefficient2Chunk4
    remainder2Coefficient2Chunk3
    remainder2Coefficient2Chunk2
    remainder2Coefficient2Chunk1
    remainder2Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A2_coeff_43 :
    remainder2Coefficient2.coeff 43 =
      (-272368018417738155386465688834341829656727182307 : ℚ) := by
  unfold
    remainder2Coefficient2
    remainder2Coefficient2Block1
    remainder2Coefficient2Block0
    remainder2Coefficient2Chunk13
    remainder2Coefficient2Chunk12
    remainder2Coefficient2Chunk11
    remainder2Coefficient2Chunk10
    remainder2Coefficient2Chunk9
    remainder2Coefficient2Chunk8
    remainder2Coefficient2Chunk7
    remainder2Coefficient2Chunk6
    remainder2Coefficient2Chunk5
    remainder2Coefficient2Chunk4
    remainder2Coefficient2Chunk3
    remainder2Coefficient2Chunk2
    remainder2Coefficient2Chunk1
    remainder2Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A2_coeff_44 :
    remainder2Coefficient2.coeff 44 =
      (1744552560514683292522850401633464103487164073490 : ℚ) := by
  unfold
    remainder2Coefficient2
    remainder2Coefficient2Block1
    remainder2Coefficient2Block0
    remainder2Coefficient2Chunk13
    remainder2Coefficient2Chunk12
    remainder2Coefficient2Chunk11
    remainder2Coefficient2Chunk10
    remainder2Coefficient2Chunk9
    remainder2Coefficient2Chunk8
    remainder2Coefficient2Chunk7
    remainder2Coefficient2Chunk6
    remainder2Coefficient2Chunk5
    remainder2Coefficient2Chunk4
    remainder2Coefficient2Chunk3
    remainder2Coefficient2Chunk2
    remainder2Coefficient2Chunk1
    remainder2Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A2_coeff_45 :
    remainder2Coefficient2.coeff 45 =
      (-1198159366924519362911282886347893563461138591211 : ℚ) := by
  unfold
    remainder2Coefficient2
    remainder2Coefficient2Block1
    remainder2Coefficient2Block0
    remainder2Coefficient2Chunk13
    remainder2Coefficient2Chunk12
    remainder2Coefficient2Chunk11
    remainder2Coefficient2Chunk10
    remainder2Coefficient2Chunk9
    remainder2Coefficient2Chunk8
    remainder2Coefficient2Chunk7
    remainder2Coefficient2Chunk6
    remainder2Coefficient2Chunk5
    remainder2Coefficient2Chunk4
    remainder2Coefficient2Chunk3
    remainder2Coefficient2Chunk2
    remainder2Coefficient2Chunk1
    remainder2Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A2_coeff_46 :
    remainder2Coefficient2.coeff 46 =
      (-13522380586587904137675170102049123376972642598255 : ℚ) := by
  unfold
    remainder2Coefficient2
    remainder2Coefficient2Block1
    remainder2Coefficient2Block0
    remainder2Coefficient2Chunk13
    remainder2Coefficient2Chunk12
    remainder2Coefficient2Chunk11
    remainder2Coefficient2Chunk10
    remainder2Coefficient2Chunk9
    remainder2Coefficient2Chunk8
    remainder2Coefficient2Chunk7
    remainder2Coefficient2Chunk6
    remainder2Coefficient2Chunk5
    remainder2Coefficient2Chunk4
    remainder2Coefficient2Chunk3
    remainder2Coefficient2Chunk2
    remainder2Coefficient2Chunk1
    remainder2Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A2_coeff_47 :
    remainder2Coefficient2.coeff 47 =
      (42291960744969586573911774792841144736581005599284 : ℚ) := by
  unfold
    remainder2Coefficient2
    remainder2Coefficient2Block1
    remainder2Coefficient2Block0
    remainder2Coefficient2Chunk13
    remainder2Coefficient2Chunk12
    remainder2Coefficient2Chunk11
    remainder2Coefficient2Chunk10
    remainder2Coefficient2Chunk9
    remainder2Coefficient2Chunk8
    remainder2Coefficient2Chunk7
    remainder2Coefficient2Chunk6
    remainder2Coefficient2Chunk5
    remainder2Coefficient2Chunk4
    remainder2Coefficient2Chunk3
    remainder2Coefficient2Chunk2
    remainder2Coefficient2Chunk1
    remainder2Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A2_coeff_48 :
    remainder2Coefficient2.coeff 48 =
      (8750926432463064317977843549196908261718546612891 : ℚ) := by
  unfold
    remainder2Coefficient2
    remainder2Coefficient2Block1
    remainder2Coefficient2Block0
    remainder2Coefficient2Chunk13
    remainder2Coefficient2Chunk12
    remainder2Coefficient2Chunk11
    remainder2Coefficient2Chunk10
    remainder2Coefficient2Chunk9
    remainder2Coefficient2Chunk8
    remainder2Coefficient2Chunk7
    remainder2Coefficient2Chunk6
    remainder2Coefficient2Chunk5
    remainder2Coefficient2Chunk4
    remainder2Coefficient2Chunk3
    remainder2Coefficient2Chunk2
    remainder2Coefficient2Chunk1
    remainder2Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A2_coeff_49 :
    remainder2Coefficient2.coeff 49 =
      (-344058533433772745293613097758239454232314009302575 : ℚ) := by
  unfold
    remainder2Coefficient2
    remainder2Coefficient2Block1
    remainder2Coefficient2Block0
    remainder2Coefficient2Chunk13
    remainder2Coefficient2Chunk12
    remainder2Coefficient2Chunk11
    remainder2Coefficient2Chunk10
    remainder2Coefficient2Chunk9
    remainder2Coefficient2Chunk8
    remainder2Coefficient2Chunk7
    remainder2Coefficient2Chunk6
    remainder2Coefficient2Chunk5
    remainder2Coefficient2Chunk4
    remainder2Coefficient2Chunk3
    remainder2Coefficient2Chunk2
    remainder2Coefficient2Chunk1
    remainder2Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A2_coeff_50 :
    remainder2Coefficient2.coeff 50 =
      (793414301057079276958444135752994668657004652391566 : ℚ) := by
  unfold
    remainder2Coefficient2
    remainder2Coefficient2Block1
    remainder2Coefficient2Block0
    remainder2Coefficient2Chunk13
    remainder2Coefficient2Chunk12
    remainder2Coefficient2Chunk11
    remainder2Coefficient2Chunk10
    remainder2Coefficient2Chunk9
    remainder2Coefficient2Chunk8
    remainder2Coefficient2Chunk7
    remainder2Coefficient2Chunk6
    remainder2Coefficient2Chunk5
    remainder2Coefficient2Chunk4
    remainder2Coefficient2Chunk3
    remainder2Coefficient2Chunk2
    remainder2Coefficient2Chunk1
    remainder2Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A2_coeff_51 :
    remainder2Coefficient2.coeff 51 =
      (286105840767256631723520274510890065023572362924729 : ℚ) := by
  unfold
    remainder2Coefficient2
    remainder2Coefficient2Block1
    remainder2Coefficient2Block0
    remainder2Coefficient2Chunk13
    remainder2Coefficient2Chunk12
    remainder2Coefficient2Chunk11
    remainder2Coefficient2Chunk10
    remainder2Coefficient2Chunk9
    remainder2Coefficient2Chunk8
    remainder2Coefficient2Chunk7
    remainder2Coefficient2Chunk6
    remainder2Coefficient2Chunk5
    remainder2Coefficient2Chunk4
    remainder2Coefficient2Chunk3
    remainder2Coefficient2Chunk2
    remainder2Coefficient2Chunk1
    remainder2Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A2_coeff_52 :
    remainder2Coefficient2.coeff 52 =
      (-5647611372358746763496541225068797862088473076319126 : ℚ) := by
  unfold
    remainder2Coefficient2
    remainder2Coefficient2Block1
    remainder2Coefficient2Block0
    remainder2Coefficient2Chunk13
    remainder2Coefficient2Chunk12
    remainder2Coefficient2Chunk11
    remainder2Coefficient2Chunk10
    remainder2Coefficient2Chunk9
    remainder2Coefficient2Chunk8
    remainder2Coefficient2Chunk7
    remainder2Coefficient2Chunk6
    remainder2Coefficient2Chunk5
    remainder2Coefficient2Chunk4
    remainder2Coefficient2Chunk3
    remainder2Coefficient2Chunk2
    remainder2Coefficient2Chunk1
    remainder2Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A2_coeff_53 :
    remainder2Coefficient2.coeff 53 =
      (12919974019283142044299163386735064499292846351870647 : ℚ) := by
  unfold
    remainder2Coefficient2
    remainder2Coefficient2Block1
    remainder2Coefficient2Block0
    remainder2Coefficient2Chunk13
    remainder2Coefficient2Chunk12
    remainder2Coefficient2Chunk11
    remainder2Coefficient2Chunk10
    remainder2Coefficient2Chunk9
    remainder2Coefficient2Chunk8
    remainder2Coefficient2Chunk7
    remainder2Coefficient2Chunk6
    remainder2Coefficient2Chunk5
    remainder2Coefficient2Chunk4
    remainder2Coefficient2Chunk3
    remainder2Coefficient2Chunk2
    remainder2Coefficient2Chunk1
    remainder2Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A2_coeff_54 :
    remainder2Coefficient2.coeff 54 =
      (-3359642529712813552784602758031437157300360833007150 : ℚ) := by
  unfold
    remainder2Coefficient2
    remainder2Coefficient2Block1
    remainder2Coefficient2Block0
    remainder2Coefficient2Chunk13
    remainder2Coefficient2Chunk12
    remainder2Coefficient2Chunk11
    remainder2Coefficient2Chunk10
    remainder2Coefficient2Chunk9
    remainder2Coefficient2Chunk8
    remainder2Coefficient2Chunk7
    remainder2Coefficient2Chunk6
    remainder2Coefficient2Chunk5
    remainder2Coefficient2Chunk4
    remainder2Coefficient2Chunk3
    remainder2Coefficient2Chunk2
    remainder2Coefficient2Chunk1
    remainder2Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A2_coeff_55 :
    remainder2Coefficient2.coeff 55 =
      (-55264383613182431624803628335662273260436933996676443 : ℚ) := by
  unfold
    remainder2Coefficient2
    remainder2Coefficient2Block1
    remainder2Coefficient2Block0
    remainder2Coefficient2Chunk13
    remainder2Coefficient2Chunk12
    remainder2Coefficient2Chunk11
    remainder2Coefficient2Chunk10
    remainder2Coefficient2Chunk9
    remainder2Coefficient2Chunk8
    remainder2Coefficient2Chunk7
    remainder2Coefficient2Chunk6
    remainder2Coefficient2Chunk5
    remainder2Coefficient2Chunk4
    remainder2Coefficient2Chunk3
    remainder2Coefficient2Chunk2
    remainder2Coefficient2Chunk1
    remainder2Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
