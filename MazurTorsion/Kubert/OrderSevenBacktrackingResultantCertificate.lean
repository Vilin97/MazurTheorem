/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Foundations.Polynomial.BoundedResultant
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData6
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantFactors
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.NormNum

/-!
# Generic resultant certificate for order-seven backtracking

This file checks the degree and leading-coefficient side conditions
for the primitive pseudo-remainder sequence and telescopes its seven
recurrences to the factored generic resultant. The recurrence proofs
are separate exact-arithmetic certificate shards.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

open MazurTorsion.PolynomialResultant

namespace Internal.ResultantCertificate

private lemma natDegree_add_le_of_le
    {p q : Bivariate} {n : ℕ}
    (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n) :
    (p + q).natDegree ≤ n :=
  (natDegree_add_le p q).trans (max_le hp hq)

private lemma remainder1_degree : remainder1.natDegree ≤ 7 := by
  simpa [remainder1] using divisionCofactorData0_degree

private lemma remainder2Block0_degree : remainder2Block0.natDegree ≤ 6 := by
  unfold remainder2Block0 remainder2Chunk0 remainder2Chunk1
    remainder2Chunk2 remainder2Chunk3
    remainder2Chunk4 remainder2Chunk5
    remainder2Chunk6 remainder2Chunk7
    remainder2Chunk8 remainder2Chunk9
    remainder2Chunk10 remainder2Chunk11
    term
  compute_degree

private lemma remainder2Block1_degree : remainder2Block1.natDegree ≤ 6 := by
  unfold remainder2Block1 remainder2Chunk12 remainder2Chunk13
    remainder2Chunk14 remainder2Chunk15
    remainder2Chunk16 remainder2Chunk17
    remainder2Chunk18 remainder2Chunk19
    remainder2Chunk20 remainder2Chunk21
    remainder2Chunk22 remainder2Chunk23
    term
  compute_degree
  norm_num

private lemma remainder2Block2_degree : remainder2Block2.natDegree ≤ 6 := by
  unfold remainder2Block2 remainder2Chunk24 remainder2Chunk25
    remainder2Chunk26 remainder2Chunk27
    remainder2Chunk28 remainder2Chunk29
    remainder2Chunk30 remainder2Chunk31
    remainder2Chunk32 remainder2Chunk33
    remainder2Chunk34 remainder2Chunk35
    term
  compute_degree
  norm_num

private lemma remainder2Block3_degree : remainder2Block3.natDegree ≤ 6 := by
  unfold remainder2Block3 remainder2Chunk36 remainder2Chunk37
    remainder2Chunk38 remainder2Chunk39
    remainder2Chunk40 remainder2Chunk41
    remainder2Chunk42 remainder2Chunk43
    remainder2Chunk44 remainder2Chunk45
    remainder2Chunk46 remainder2Chunk47
    term
  compute_degree
  norm_num

private lemma remainder2Block4_degree : remainder2Block4.natDegree ≤ 6 := by
  unfold remainder2Block4 remainder2Chunk48 remainder2Chunk49
    remainder2Chunk50 remainder2Chunk51
    remainder2Chunk52 remainder2Chunk53
    remainder2Chunk54 remainder2Chunk55
    remainder2Chunk56 remainder2Chunk57
    remainder2Chunk58 remainder2Chunk59
    term
  compute_degree
  norm_num

private lemma remainder2Block5_degree : remainder2Block5.natDegree ≤ 6 := by
  unfold remainder2Block5 remainder2Chunk60 remainder2Chunk61
    remainder2Chunk62 remainder2Chunk63
    remainder2Chunk64 remainder2Chunk65
    remainder2Chunk66 remainder2Chunk67
    remainder2Chunk68 remainder2Chunk69
    remainder2Chunk70 remainder2Chunk71
    term
  compute_degree
  norm_num

private lemma remainder2Block6_degree : remainder2Block6.natDegree ≤ 6 := by
  unfold remainder2Block6 remainder2Chunk72 remainder2Chunk73
    remainder2Chunk74 remainder2Chunk75
    remainder2Chunk76 remainder2Chunk77
    remainder2Chunk78 remainder2Chunk79
    remainder2Chunk80 remainder2Chunk81
    remainder2Chunk82 remainder2Chunk83
    term
  compute_degree
  norm_num

private lemma remainder2Block7_degree : remainder2Block7.natDegree ≤ 6 := by
  unfold remainder2Block7 remainder2Chunk84 remainder2Chunk85
    remainder2Chunk86 remainder2Chunk87
    remainder2Chunk88 remainder2Chunk89
    remainder2Chunk90 remainder2Chunk91
    remainder2Chunk92 term
  compute_degree
  norm_num

private lemma remainder2_degree : remainder2.natDegree ≤ 6 := by
  unfold remainder2
  apply natDegree_add_le_of_le
  · apply natDegree_add_le_of_le
    · apply natDegree_add_le_of_le
      · apply natDegree_add_le_of_le
        · apply natDegree_add_le_of_le
          · apply natDegree_add_le_of_le
            · apply natDegree_add_le_of_le
              · exact remainder2Block0_degree
              · exact remainder2Block1_degree
            · exact remainder2Block2_degree
          · exact remainder2Block3_degree
        · exact remainder2Block4_degree
      · exact remainder2Block5_degree
    · exact remainder2Block6_degree
  · exact remainder2Block7_degree

private lemma remainder3Block0_degree : remainder3Block0.natDegree ≤ 5 := by
  unfold remainder3Block0 remainder3Chunk0 remainder3Chunk1
    remainder3Chunk2 remainder3Chunk3
    remainder3Chunk4 remainder3Chunk5
    remainder3Chunk6 remainder3Chunk7
    remainder3Chunk8 remainder3Chunk9
    remainder3Chunk10 remainder3Chunk11
    term
  compute_degree

private lemma remainder3Block1_degree : remainder3Block1.natDegree ≤ 5 := by
  unfold remainder3Block1 remainder3Chunk12 remainder3Chunk13
    remainder3Chunk14 remainder3Chunk15
    remainder3Chunk16 remainder3Chunk17
    remainder3Chunk18 remainder3Chunk19
    remainder3Chunk20 remainder3Chunk21
    remainder3Chunk22 remainder3Chunk23
    term
  compute_degree

private lemma remainder3Block2_degree : remainder3Block2.natDegree ≤ 5 := by
  unfold remainder3Block2 remainder3Chunk24 remainder3Chunk25
    remainder3Chunk26 remainder3Chunk27
    remainder3Chunk28 remainder3Chunk29
    remainder3Chunk30 remainder3Chunk31
    remainder3Chunk32 remainder3Chunk33
    remainder3Chunk34 remainder3Chunk35
    term
  compute_degree
  norm_num

private lemma remainder3Block3_degree : remainder3Block3.natDegree ≤ 5 := by
  unfold remainder3Block3 remainder3Chunk36 remainder3Chunk37
    remainder3Chunk38 remainder3Chunk39
    remainder3Chunk40 remainder3Chunk41
    remainder3Chunk42 remainder3Chunk43
    remainder3Chunk44 remainder3Chunk45
    remainder3Chunk46 remainder3Chunk47
    term
  compute_degree
  norm_num

private lemma remainder3Block4_degree : remainder3Block4.natDegree ≤ 5 := by
  unfold remainder3Block4 remainder3Chunk48 remainder3Chunk49
    remainder3Chunk50 remainder3Chunk51
    remainder3Chunk52 remainder3Chunk53
    remainder3Chunk54 remainder3Chunk55
    remainder3Chunk56 remainder3Chunk57
    remainder3Chunk58 remainder3Chunk59
    term
  compute_degree
  norm_num

private lemma remainder3Block5_degree : remainder3Block5.natDegree ≤ 5 := by
  unfold remainder3Block5 remainder3Chunk60 remainder3Chunk61
    remainder3Chunk62 remainder3Chunk63
    remainder3Chunk64 remainder3Chunk65
    remainder3Chunk66 remainder3Chunk67
    remainder3Chunk68 remainder3Chunk69
    remainder3Chunk70 remainder3Chunk71
    term
  compute_degree
  norm_num

private lemma remainder3Block6_degree : remainder3Block6.natDegree ≤ 5 := by
  unfold remainder3Block6 remainder3Chunk72 remainder3Chunk73
    remainder3Chunk74 remainder3Chunk75
    remainder3Chunk76 remainder3Chunk77
    remainder3Chunk78 remainder3Chunk79
    remainder3Chunk80 remainder3Chunk81
    remainder3Chunk82 remainder3Chunk83
    term
  compute_degree
  norm_num

private lemma remainder3Block7_degree : remainder3Block7.natDegree ≤ 5 := by
  unfold remainder3Block7 remainder3Chunk84 remainder3Chunk85
    remainder3Chunk86 remainder3Chunk87
    remainder3Chunk88 remainder3Chunk89
    remainder3Chunk90 remainder3Chunk91
    remainder3Chunk92 remainder3Chunk93
    remainder3Chunk94 remainder3Chunk95
    term
  compute_degree
  norm_num

private lemma remainder3Block8_degree : remainder3Block8.natDegree ≤ 5 := by
  unfold remainder3Block8 remainder3Chunk96 remainder3Chunk97
    remainder3Chunk98 remainder3Chunk99
    remainder3Chunk100 remainder3Chunk101
    remainder3Chunk102 remainder3Chunk103
    remainder3Chunk104 remainder3Chunk105
    remainder3Chunk106 remainder3Chunk107
    term
  compute_degree
  norm_num

private lemma remainder3_degree : remainder3.natDegree ≤ 5 := by
  unfold remainder3
  apply natDegree_add_le_of_le
  · apply natDegree_add_le_of_le
    · apply natDegree_add_le_of_le
      · apply natDegree_add_le_of_le
        · apply natDegree_add_le_of_le
          · apply natDegree_add_le_of_le
            · apply natDegree_add_le_of_le
              · apply natDegree_add_le_of_le
                · exact remainder3Block0_degree
                · exact remainder3Block1_degree
              · exact remainder3Block2_degree
            · exact remainder3Block3_degree
          · exact remainder3Block4_degree
        · exact remainder3Block5_degree
      · exact remainder3Block6_degree
    · exact remainder3Block7_degree
  · exact remainder3Block8_degree

private lemma remainder4Block0_degree : remainder4Block0.natDegree ≤ 4 := by
  unfold remainder4Block0 remainder4Chunk0 remainder4Chunk1
    remainder4Chunk2 remainder4Chunk3
    remainder4Chunk4 remainder4Chunk5
    remainder4Chunk6 remainder4Chunk7
    remainder4Chunk8 remainder4Chunk9
    remainder4Chunk10 remainder4Chunk11
    term
  compute_degree

private lemma remainder4Block1_degree : remainder4Block1.natDegree ≤ 4 := by
  unfold remainder4Block1 remainder4Chunk12 remainder4Chunk13
    remainder4Chunk14 remainder4Chunk15
    remainder4Chunk16 remainder4Chunk17
    remainder4Chunk18 remainder4Chunk19
    remainder4Chunk20 remainder4Chunk21
    remainder4Chunk22 remainder4Chunk23
    term
  compute_degree

private lemma remainder4Block2_degree : remainder4Block2.natDegree ≤ 4 := by
  unfold remainder4Block2 remainder4Chunk24 remainder4Chunk25
    remainder4Chunk26 remainder4Chunk27
    remainder4Chunk28 remainder4Chunk29
    remainder4Chunk30 remainder4Chunk31
    remainder4Chunk32 remainder4Chunk33
    remainder4Chunk34 remainder4Chunk35
    term
  compute_degree
  norm_num

private lemma remainder4Block3_degree : remainder4Block3.natDegree ≤ 4 := by
  unfold remainder4Block3 remainder4Chunk36 remainder4Chunk37
    remainder4Chunk38 remainder4Chunk39
    remainder4Chunk40 remainder4Chunk41
    remainder4Chunk42 remainder4Chunk43
    remainder4Chunk44 remainder4Chunk45
    remainder4Chunk46 remainder4Chunk47
    term
  compute_degree
  norm_num

private lemma remainder4Block4_degree : remainder4Block4.natDegree ≤ 4 := by
  unfold remainder4Block4 remainder4Chunk48 remainder4Chunk49
    remainder4Chunk50 remainder4Chunk51
    remainder4Chunk52 remainder4Chunk53
    remainder4Chunk54 remainder4Chunk55
    remainder4Chunk56 remainder4Chunk57
    remainder4Chunk58 remainder4Chunk59
    term
  compute_degree
  norm_num

private lemma remainder4Block5_degree : remainder4Block5.natDegree ≤ 4 := by
  unfold remainder4Block5 remainder4Chunk60 remainder4Chunk61
    remainder4Chunk62 remainder4Chunk63
    remainder4Chunk64 remainder4Chunk65
    remainder4Chunk66 remainder4Chunk67
    remainder4Chunk68 remainder4Chunk69
    remainder4Chunk70 remainder4Chunk71
    term
  compute_degree
  norm_num

private lemma remainder4Block6_degree : remainder4Block6.natDegree ≤ 4 := by
  unfold remainder4Block6 remainder4Chunk72 remainder4Chunk73
    remainder4Chunk74 remainder4Chunk75
    remainder4Chunk76 remainder4Chunk77
    remainder4Chunk78 remainder4Chunk79
    remainder4Chunk80 remainder4Chunk81
    remainder4Chunk82 remainder4Chunk83
    term
  compute_degree
  norm_num

private lemma remainder4Block7_degree : remainder4Block7.natDegree ≤ 4 := by
  unfold remainder4Block7 remainder4Chunk84 remainder4Chunk85
    remainder4Chunk86 remainder4Chunk87
    remainder4Chunk88 remainder4Chunk89
    remainder4Chunk90 remainder4Chunk91
    remainder4Chunk92 remainder4Chunk93
    remainder4Chunk94 remainder4Chunk95
    term
  compute_degree
  norm_num

private lemma remainder4Block8_degree : remainder4Block8.natDegree ≤ 4 := by
  unfold remainder4Block8 remainder4Chunk96 remainder4Chunk97
    remainder4Chunk98 remainder4Chunk99
    remainder4Chunk100 remainder4Chunk101
    remainder4Chunk102 remainder4Chunk103
    remainder4Chunk104 remainder4Chunk105
    remainder4Chunk106 remainder4Chunk107
    term
  compute_degree
  norm_num

private lemma remainder4Block9_degree : remainder4Block9.natDegree ≤ 4 := by
  unfold remainder4Block9 remainder4Chunk108 remainder4Chunk109
    remainder4Chunk110 remainder4Chunk111
    remainder4Chunk112 remainder4Chunk113
    remainder4Chunk114 remainder4Chunk115
    remainder4Chunk116 term
  compute_degree
  norm_num

private lemma remainder4_degree : remainder4.natDegree ≤ 4 := by
  unfold remainder4
  apply natDegree_add_le_of_le
  · apply natDegree_add_le_of_le
    · apply natDegree_add_le_of_le
      · apply natDegree_add_le_of_le
        · apply natDegree_add_le_of_le
          · apply natDegree_add_le_of_le
            · apply natDegree_add_le_of_le
              · apply natDegree_add_le_of_le
                · apply natDegree_add_le_of_le
                  · exact remainder4Block0_degree
                  · exact remainder4Block1_degree
                · exact remainder4Block2_degree
              · exact remainder4Block3_degree
            · exact remainder4Block4_degree
          · exact remainder4Block5_degree
        · exact remainder4Block6_degree
      · exact remainder4Block7_degree
    · exact remainder4Block8_degree
  · exact remainder4Block9_degree

private lemma remainder5Block0_degree : remainder5Block0.natDegree ≤ 3 := by
  unfold remainder5Block0 remainder5Chunk0 remainder5Chunk1
    remainder5Chunk2 remainder5Chunk3
    remainder5Chunk4 remainder5Chunk5
    remainder5Chunk6 remainder5Chunk7
    remainder5Chunk8 remainder5Chunk9
    remainder5Chunk10 remainder5Chunk11
    term
  compute_degree

private lemma remainder5Block1_degree : remainder5Block1.natDegree ≤ 3 := by
  unfold remainder5Block1 remainder5Chunk12 remainder5Chunk13
    remainder5Chunk14 remainder5Chunk15
    remainder5Chunk16 remainder5Chunk17
    remainder5Chunk18 remainder5Chunk19
    remainder5Chunk20 remainder5Chunk21
    remainder5Chunk22 remainder5Chunk23
    term
  compute_degree

private lemma remainder5Block2_degree : remainder5Block2.natDegree ≤ 3 := by
  unfold remainder5Block2 remainder5Chunk24 remainder5Chunk25
    remainder5Chunk26 remainder5Chunk27
    remainder5Chunk28 remainder5Chunk29
    remainder5Chunk30 remainder5Chunk31
    remainder5Chunk32 remainder5Chunk33
    remainder5Chunk34 remainder5Chunk35
    term
  compute_degree
  norm_num

private lemma remainder5Block3_degree : remainder5Block3.natDegree ≤ 3 := by
  unfold remainder5Block3 remainder5Chunk36 remainder5Chunk37
    remainder5Chunk38 remainder5Chunk39
    remainder5Chunk40 remainder5Chunk41
    remainder5Chunk42 remainder5Chunk43
    remainder5Chunk44 remainder5Chunk45
    remainder5Chunk46 remainder5Chunk47
    term
  compute_degree
  norm_num

private lemma remainder5Block4_degree : remainder5Block4.natDegree ≤ 3 := by
  unfold remainder5Block4 remainder5Chunk48 remainder5Chunk49
    remainder5Chunk50 remainder5Chunk51
    remainder5Chunk52 remainder5Chunk53
    remainder5Chunk54 remainder5Chunk55
    remainder5Chunk56 remainder5Chunk57
    remainder5Chunk58 remainder5Chunk59
    term
  compute_degree
  norm_num

private lemma remainder5Block5_degree : remainder5Block5.natDegree ≤ 3 := by
  unfold remainder5Block5 remainder5Chunk60 remainder5Chunk61
    remainder5Chunk62 remainder5Chunk63
    remainder5Chunk64 remainder5Chunk65
    remainder5Chunk66 remainder5Chunk67
    remainder5Chunk68 remainder5Chunk69
    remainder5Chunk70 remainder5Chunk71
    term
  compute_degree
  norm_num

private lemma remainder5Block6_degree : remainder5Block6.natDegree ≤ 3 := by
  unfold remainder5Block6 remainder5Chunk72 remainder5Chunk73
    remainder5Chunk74 remainder5Chunk75
    remainder5Chunk76 remainder5Chunk77
    remainder5Chunk78 remainder5Chunk79
    remainder5Chunk80 remainder5Chunk81
    remainder5Chunk82 remainder5Chunk83
    term
  compute_degree
  norm_num

private lemma remainder5Block7_degree : remainder5Block7.natDegree ≤ 3 := by
  unfold remainder5Block7 remainder5Chunk84 remainder5Chunk85
    term
  compute_degree
  norm_num

private lemma remainder5_degree : remainder5.natDegree ≤ 3 := by
  unfold remainder5
  apply natDegree_add_le_of_le
  · apply natDegree_add_le_of_le
    · apply natDegree_add_le_of_le
      · apply natDegree_add_le_of_le
        · apply natDegree_add_le_of_le
          · apply natDegree_add_le_of_le
            · apply natDegree_add_le_of_le
              · exact remainder5Block0_degree
              · exact remainder5Block1_degree
            · exact remainder5Block2_degree
          · exact remainder5Block3_degree
        · exact remainder5Block4_degree
      · exact remainder5Block5_degree
    · exact remainder5Block6_degree
  · exact remainder5Block7_degree

private lemma remainder6Block0_degree : remainder6Block0.natDegree ≤ 2 := by
  unfold remainder6Block0 remainder6Chunk0 remainder6Chunk1
    remainder6Chunk2 remainder6Chunk3
    remainder6Chunk4 remainder6Chunk5
    remainder6Chunk6 remainder6Chunk7
    remainder6Chunk8 remainder6Chunk9
    remainder6Chunk10 remainder6Chunk11
    term
  compute_degree

private lemma remainder6Block1_degree : remainder6Block1.natDegree ≤ 2 := by
  unfold remainder6Block1 remainder6Chunk12 remainder6Chunk13
    remainder6Chunk14 remainder6Chunk15
    remainder6Chunk16 remainder6Chunk17
    remainder6Chunk18 remainder6Chunk19
    remainder6Chunk20 remainder6Chunk21
    remainder6Chunk22 remainder6Chunk23
    term
  compute_degree

private lemma remainder6Block2_degree : remainder6Block2.natDegree ≤ 2 := by
  unfold remainder6Block2 remainder6Chunk24 remainder6Chunk25
    remainder6Chunk26 remainder6Chunk27
    remainder6Chunk28 remainder6Chunk29
    remainder6Chunk30 remainder6Chunk31
    remainder6Chunk32 remainder6Chunk33
    remainder6Chunk34 remainder6Chunk35
    term
  compute_degree
  norm_num

private lemma remainder6Block3_degree : remainder6Block3.natDegree ≤ 2 := by
  unfold remainder6Block3 remainder6Chunk36 remainder6Chunk37
    remainder6Chunk38 remainder6Chunk39
    remainder6Chunk40 remainder6Chunk41
    remainder6Chunk42 remainder6Chunk43
    remainder6Chunk44 remainder6Chunk45
    remainder6Chunk46 remainder6Chunk47
    term
  compute_degree
  norm_num

private lemma remainder6Block4_degree : remainder6Block4.natDegree ≤ 2 := by
  unfold remainder6Block4 remainder6Chunk48 remainder6Chunk49
    remainder6Chunk50 remainder6Chunk51
    remainder6Chunk52 remainder6Chunk53
    remainder6Chunk54 remainder6Chunk55
    term
  compute_degree
  norm_num

private lemma remainder6_degree : remainder6.natDegree ≤ 2 := by
  unfold remainder6
  apply natDegree_add_le_of_le
  · apply natDegree_add_le_of_le
    · apply natDegree_add_le_of_le
      · apply natDegree_add_le_of_le
        · exact remainder6Block0_degree
        · exact remainder6Block1_degree
      · exact remainder6Block2_degree
    · exact remainder6Block3_degree
  · exact remainder6Block4_degree

private lemma remainder7Block0_degree : remainder7Block0.natDegree ≤ 1 := by
  unfold remainder7Block0 remainder7Chunk0 remainder7Chunk1
    remainder7Chunk2 remainder7Chunk3
    remainder7Chunk4 remainder7Chunk5
    remainder7Chunk6 remainder7Chunk7
    remainder7Chunk8 remainder7Chunk9
    remainder7Chunk10 remainder7Chunk11
    term
  compute_degree

private lemma remainder7Block1_degree : remainder7Block1.natDegree ≤ 1 := by
  unfold remainder7Block1 remainder7Chunk12 remainder7Chunk13
    remainder7Chunk14 remainder7Chunk15
    remainder7Chunk16 remainder7Chunk17
    remainder7Chunk18 remainder7Chunk19
    remainder7Chunk20 remainder7Chunk21
    term
  compute_degree
  norm_num

private lemma remainder7_degree : remainder7.natDegree ≤ 1 := by
  unfold remainder7
  apply natDegree_add_le_of_le
  · exact remainder7Block0_degree
  · exact remainder7Block1_degree

private lemma remainder8Block0_degree : remainder8Block0.natDegree ≤ 0 := by
  unfold remainder8Block0 remainder8Chunk0 term
  compute_degree

private lemma remainder8_degree : remainder8.natDegree ≤ 0 := by
  unfold remainder8
  exact remainder8Block0_degree

private lemma quotient0Block0_degree : quotient0Block0.natDegree ≤ 26 := by
  unfold quotient0Block0 quotient0Chunk0 quotient0Chunk1
    quotient0Chunk2 quotient0Chunk3
    quotient0Chunk4 quotient0Chunk5
    quotient0Chunk6 quotient0Chunk7
    quotient0Chunk8 quotient0Chunk9
    quotient0Chunk10 quotient0Chunk11
    term
  compute_degree

private lemma quotient0Block1_degree : quotient0Block1.natDegree ≤ 26 := by
  unfold quotient0Block1 quotient0Chunk12 quotient0Chunk13
    quotient0Chunk14 quotient0Chunk15
    quotient0Chunk16 quotient0Chunk17
    quotient0Chunk18 quotient0Chunk19
    quotient0Chunk20 quotient0Chunk21
    quotient0Chunk22 quotient0Chunk23
    term
  compute_degree
  norm_num

private lemma quotient0Block2_degree : quotient0Block2.natDegree ≤ 26 := by
  unfold quotient0Block2 quotient0Chunk24 quotient0Chunk25
    quotient0Chunk26 quotient0Chunk27
    quotient0Chunk28 quotient0Chunk29
    quotient0Chunk30 quotient0Chunk31
    quotient0Chunk32 quotient0Chunk33
    quotient0Chunk34 quotient0Chunk35
    term
  compute_degree
  norm_num

private lemma quotient0Block3_degree : quotient0Block3.natDegree ≤ 26 := by
  unfold quotient0Block3 quotient0Chunk36 quotient0Chunk37
    quotient0Chunk38 quotient0Chunk39
    quotient0Chunk40 quotient0Chunk41
    quotient0Chunk42 quotient0Chunk43
    quotient0Chunk44 quotient0Chunk45
    quotient0Chunk46 quotient0Chunk47
    term
  compute_degree
  norm_num

private lemma quotient0Block4_degree : quotient0Block4.natDegree ≤ 26 := by
  unfold quotient0Block4 quotient0Chunk48 quotient0Chunk49
    quotient0Chunk50 quotient0Chunk51
    quotient0Chunk52 quotient0Chunk53
    quotient0Chunk54 quotient0Chunk55
    quotient0Chunk56 quotient0Chunk57
    quotient0Chunk58 quotient0Chunk59
    term
  compute_degree
  norm_num

private lemma quotient0Block5_degree : quotient0Block5.natDegree ≤ 26 := by
  unfold quotient0Block5 quotient0Chunk60 quotient0Chunk61
    quotient0Chunk62 quotient0Chunk63
    quotient0Chunk64 quotient0Chunk65
    quotient0Chunk66 quotient0Chunk67
    quotient0Chunk68 quotient0Chunk69
    quotient0Chunk70 quotient0Chunk71
    term
  compute_degree
  norm_num

private lemma quotient0Block6_degree : quotient0Block6.natDegree ≤ 26 := by
  unfold quotient0Block6 quotient0Chunk72 quotient0Chunk73
    quotient0Chunk74 quotient0Chunk75
    quotient0Chunk76 quotient0Chunk77
    quotient0Chunk78 quotient0Chunk79
    quotient0Chunk80 quotient0Chunk81
    quotient0Chunk82 quotient0Chunk83
    term
  compute_degree
  norm_num

private lemma quotient0Block7_degree : quotient0Block7.natDegree ≤ 26 := by
  unfold quotient0Block7 quotient0Chunk84 quotient0Chunk85
    quotient0Chunk86 quotient0Chunk87
    quotient0Chunk88 quotient0Chunk89
    quotient0Chunk90 quotient0Chunk91
    quotient0Chunk92 quotient0Chunk93
    quotient0Chunk94 quotient0Chunk95
    term
  compute_degree
  norm_num

private lemma quotient0Block8_degree : quotient0Block8.natDegree ≤ 26 := by
  unfold quotient0Block8 quotient0Chunk96 quotient0Chunk97
    quotient0Chunk98 quotient0Chunk99
    quotient0Chunk100 quotient0Chunk101
    quotient0Chunk102 quotient0Chunk103
    quotient0Chunk104 quotient0Chunk105
    quotient0Chunk106 quotient0Chunk107
    term
  compute_degree
  norm_num

private lemma quotient0Block9_degree : quotient0Block9.natDegree ≤ 26 := by
  unfold quotient0Block9 quotient0Chunk108 quotient0Chunk109
    quotient0Chunk110 quotient0Chunk111
    quotient0Chunk112 quotient0Chunk113
    quotient0Chunk114 quotient0Chunk115
    quotient0Chunk116 quotient0Chunk117
    quotient0Chunk118 quotient0Chunk119
    term
  compute_degree
  norm_num

private lemma quotient0Block10_degree : quotient0Block10.natDegree ≤ 26 := by
  unfold quotient0Block10 quotient0Chunk120 quotient0Chunk121
    quotient0Chunk122 quotient0Chunk123
    quotient0Chunk124 quotient0Chunk125
    quotient0Chunk126 quotient0Chunk127
    quotient0Chunk128 quotient0Chunk129
    quotient0Chunk130 quotient0Chunk131
    term
  compute_degree
  norm_num

private lemma quotient0Block11_degree : quotient0Block11.natDegree ≤ 26 := by
  unfold quotient0Block11 quotient0Chunk132 quotient0Chunk133
    quotient0Chunk134 quotient0Chunk135
    quotient0Chunk136 quotient0Chunk137
    quotient0Chunk138 quotient0Chunk139
    quotient0Chunk140 quotient0Chunk141
    quotient0Chunk142 quotient0Chunk143
    term
  compute_degree
  norm_num

private lemma quotient0Block12_degree : quotient0Block12.natDegree ≤ 26 := by
  unfold quotient0Block12 quotient0Chunk144 quotient0Chunk145
    quotient0Chunk146 quotient0Chunk147
    quotient0Chunk148 quotient0Chunk149
    quotient0Chunk150 quotient0Chunk151
    quotient0Chunk152 quotient0Chunk153
    quotient0Chunk154 quotient0Chunk155
    term
  compute_degree
  norm_num

private lemma quotient0Block13_degree : quotient0Block13.natDegree ≤ 26 := by
  unfold quotient0Block13 quotient0Chunk156 quotient0Chunk157
    quotient0Chunk158 quotient0Chunk159
    quotient0Chunk160 quotient0Chunk161
    quotient0Chunk162 quotient0Chunk163
    quotient0Chunk164 quotient0Chunk165
    quotient0Chunk166 quotient0Chunk167
    term
  compute_degree
  norm_num

private lemma quotient0Block14_degree : quotient0Block14.natDegree ≤ 26 := by
  unfold quotient0Block14 quotient0Chunk168 quotient0Chunk169
    quotient0Chunk170 quotient0Chunk171
    quotient0Chunk172 quotient0Chunk173
    quotient0Chunk174 quotient0Chunk175
    term
  compute_degree
  norm_num

private lemma quotient0_degree : quotient0.natDegree ≤ 26 := by
  unfold quotient0
  apply natDegree_add_le_of_le
  · apply natDegree_add_le_of_le
    · apply natDegree_add_le_of_le
      · apply natDegree_add_le_of_le
        · apply natDegree_add_le_of_le
          · apply natDegree_add_le_of_le
            · apply natDegree_add_le_of_le
              · apply natDegree_add_le_of_le
                · apply natDegree_add_le_of_le
                  · apply natDegree_add_le_of_le
                    · apply natDegree_add_le_of_le
                      · apply natDegree_add_le_of_le
                        · apply natDegree_add_le_of_le
                          · apply natDegree_add_le_of_le
                            · exact quotient0Block0_degree
                            · exact quotient0Block1_degree
                          · exact quotient0Block2_degree
                        · exact quotient0Block3_degree
                      · exact quotient0Block4_degree
                    · exact quotient0Block5_degree
                  · exact quotient0Block6_degree
                · exact quotient0Block7_degree
              · exact quotient0Block8_degree
            · exact quotient0Block9_degree
          · exact quotient0Block10_degree
        · exact quotient0Block11_degree
      · exact quotient0Block12_degree
    · exact quotient0Block13_degree
  · exact quotient0Block14_degree

private lemma quotient1Block0_degree : quotient1Block0.natDegree ≤ 1 := by
  unfold quotient1Block0 quotient1Chunk0 quotient1Chunk1
    quotient1Chunk2 quotient1Chunk3
    quotient1Chunk4 quotient1Chunk5
    quotient1Chunk6 quotient1Chunk7
    quotient1Chunk8 quotient1Chunk9
    quotient1Chunk10 quotient1Chunk11
    term
  compute_degree

private lemma quotient1Block1_degree : quotient1Block1.natDegree ≤ 1 := by
  unfold quotient1Block1 quotient1Chunk12 quotient1Chunk13
    quotient1Chunk14 quotient1Chunk15
    quotient1Chunk16 quotient1Chunk17
    quotient1Chunk18 quotient1Chunk19
    quotient1Chunk20 quotient1Chunk21
    quotient1Chunk22 quotient1Chunk23
    term
  compute_degree
  norm_num

private lemma quotient1Block2_degree : quotient1Block2.natDegree ≤ 1 := by
  unfold quotient1Block2 quotient1Chunk24 term
  compute_degree
  norm_num

private lemma quotient1_degree : quotient1.natDegree ≤ 1 := by
  unfold quotient1
  apply natDegree_add_le_of_le
  · apply natDegree_add_le_of_le
    · exact quotient1Block0_degree
    · exact quotient1Block1_degree
  · exact quotient1Block2_degree

private lemma quotient2Block0_degree : quotient2Block0.natDegree ≤ 1 := by
  unfold quotient2Block0 quotient2Chunk0 quotient2Chunk1
    quotient2Chunk2 quotient2Chunk3
    quotient2Chunk4 quotient2Chunk5
    quotient2Chunk6 quotient2Chunk7
    quotient2Chunk8 quotient2Chunk9
    quotient2Chunk10 quotient2Chunk11
    term
  compute_degree

private lemma quotient2Block1_degree : quotient2Block1.natDegree ≤ 1 := by
  unfold quotient2Block1 quotient2Chunk12 quotient2Chunk13
    quotient2Chunk14 quotient2Chunk15
    quotient2Chunk16 quotient2Chunk17
    quotient2Chunk18 quotient2Chunk19
    quotient2Chunk20 quotient2Chunk21
    quotient2Chunk22 quotient2Chunk23
    term
  compute_degree

private lemma quotient2Block2_degree : quotient2Block2.natDegree ≤ 1 := by
  unfold quotient2Block2 quotient2Chunk24 quotient2Chunk25
    quotient2Chunk26 quotient2Chunk27
    quotient2Chunk28 quotient2Chunk29
    quotient2Chunk30 quotient2Chunk31
    quotient2Chunk32 quotient2Chunk33
    quotient2Chunk34 quotient2Chunk35
    term
  compute_degree

private lemma quotient2Block3_degree : quotient2Block3.natDegree ≤ 1 := by
  unfold quotient2Block3 quotient2Chunk36 quotient2Chunk37
    quotient2Chunk38 quotient2Chunk39
    quotient2Chunk40 quotient2Chunk41
    quotient2Chunk42 quotient2Chunk43
    quotient2Chunk44 quotient2Chunk45
    quotient2Chunk46 quotient2Chunk47
    term
  compute_degree
  norm_num

private lemma quotient2Block4_degree : quotient2Block4.natDegree ≤ 1 := by
  unfold quotient2Block4 quotient2Chunk48 quotient2Chunk49
    quotient2Chunk50 quotient2Chunk51
    quotient2Chunk52 quotient2Chunk53
    quotient2Chunk54 quotient2Chunk55
    quotient2Chunk56 quotient2Chunk57
    term
  compute_degree
  norm_num

private lemma quotient2_degree : quotient2.natDegree ≤ 1 := by
  unfold quotient2
  apply natDegree_add_le_of_le
  · apply natDegree_add_le_of_le
    · apply natDegree_add_le_of_le
      · apply natDegree_add_le_of_le
        · exact quotient2Block0_degree
        · exact quotient2Block1_degree
      · exact quotient2Block2_degree
    · exact quotient2Block3_degree
  · exact quotient2Block4_degree

private lemma quotient3Block0_degree : quotient3Block0.natDegree ≤ 1 := by
  unfold quotient3Block0 quotient3Chunk0 quotient3Chunk1
    quotient3Chunk2 quotient3Chunk3
    quotient3Chunk4 quotient3Chunk5
    quotient3Chunk6 quotient3Chunk7
    quotient3Chunk8 quotient3Chunk9
    quotient3Chunk10 quotient3Chunk11
    term
  compute_degree

private lemma quotient3Block1_degree : quotient3Block1.natDegree ≤ 1 := by
  unfold quotient3Block1 quotient3Chunk12 quotient3Chunk13
    quotient3Chunk14 quotient3Chunk15
    quotient3Chunk16 quotient3Chunk17
    quotient3Chunk18 quotient3Chunk19
    quotient3Chunk20 quotient3Chunk21
    quotient3Chunk22 quotient3Chunk23
    term
  compute_degree

private lemma quotient3Block2_degree : quotient3Block2.natDegree ≤ 1 := by
  unfold quotient3Block2 quotient3Chunk24 quotient3Chunk25
    quotient3Chunk26 quotient3Chunk27
    quotient3Chunk28 quotient3Chunk29
    quotient3Chunk30 quotient3Chunk31
    quotient3Chunk32 quotient3Chunk33
    quotient3Chunk34 quotient3Chunk35
    term
  compute_degree

private lemma quotient3Block3_degree : quotient3Block3.natDegree ≤ 1 := by
  unfold quotient3Block3 quotient3Chunk36 quotient3Chunk37
    quotient3Chunk38 quotient3Chunk39
    quotient3Chunk40 quotient3Chunk41
    quotient3Chunk42 quotient3Chunk43
    quotient3Chunk44 quotient3Chunk45
    quotient3Chunk46 quotient3Chunk47
    term
  compute_degree

private lemma quotient3Block4_degree : quotient3Block4.natDegree ≤ 1 := by
  unfold quotient3Block4 quotient3Chunk48 quotient3Chunk49
    quotient3Chunk50 quotient3Chunk51
    quotient3Chunk52 quotient3Chunk53
    quotient3Chunk54 quotient3Chunk55
    quotient3Chunk56 quotient3Chunk57
    quotient3Chunk58 quotient3Chunk59
    term
  compute_degree
  norm_num

private lemma quotient3Block5_degree : quotient3Block5.natDegree ≤ 1 := by
  unfold quotient3Block5 quotient3Chunk60 quotient3Chunk61
    quotient3Chunk62 quotient3Chunk63
    quotient3Chunk64 quotient3Chunk65
    quotient3Chunk66 quotient3Chunk67
    quotient3Chunk68 quotient3Chunk69
    quotient3Chunk70 quotient3Chunk71
    term
  compute_degree
  norm_num

private lemma quotient3Block6_degree : quotient3Block6.natDegree ≤ 1 := by
  unfold quotient3Block6 quotient3Chunk72 quotient3Chunk73
    quotient3Chunk74 quotient3Chunk75
    quotient3Chunk76 quotient3Chunk77
    quotient3Chunk78 term
  compute_degree
  norm_num

private lemma quotient3_degree : quotient3.natDegree ≤ 1 := by
  unfold quotient3
  apply natDegree_add_le_of_le
  · apply natDegree_add_le_of_le
    · apply natDegree_add_le_of_le
      · apply natDegree_add_le_of_le
        · apply natDegree_add_le_of_le
          · apply natDegree_add_le_of_le
            · exact quotient3Block0_degree
            · exact quotient3Block1_degree
          · exact quotient3Block2_degree
        · exact quotient3Block3_degree
      · exact quotient3Block4_degree
    · exact quotient3Block5_degree
  · exact quotient3Block6_degree

private lemma quotient4Block0_degree : quotient4Block0.natDegree ≤ 1 := by
  unfold quotient4Block0 quotient4Chunk0 quotient4Chunk1
    quotient4Chunk2 quotient4Chunk3
    quotient4Chunk4 quotient4Chunk5
    quotient4Chunk6 quotient4Chunk7
    quotient4Chunk8 quotient4Chunk9
    quotient4Chunk10 quotient4Chunk11
    term
  compute_degree

private lemma quotient4Block1_degree : quotient4Block1.natDegree ≤ 1 := by
  unfold quotient4Block1 quotient4Chunk12 quotient4Chunk13
    quotient4Chunk14 quotient4Chunk15
    quotient4Chunk16 quotient4Chunk17
    quotient4Chunk18 quotient4Chunk19
    quotient4Chunk20 quotient4Chunk21
    quotient4Chunk22 quotient4Chunk23
    term
  compute_degree

private lemma quotient4Block2_degree : quotient4Block2.natDegree ≤ 1 := by
  unfold quotient4Block2 quotient4Chunk24 quotient4Chunk25
    quotient4Chunk26 quotient4Chunk27
    quotient4Chunk28 quotient4Chunk29
    quotient4Chunk30 quotient4Chunk31
    quotient4Chunk32 quotient4Chunk33
    quotient4Chunk34 quotient4Chunk35
    term
  compute_degree

private lemma quotient4Block3_degree : quotient4Block3.natDegree ≤ 1 := by
  unfold quotient4Block3 quotient4Chunk36 quotient4Chunk37
    quotient4Chunk38 quotient4Chunk39
    quotient4Chunk40 quotient4Chunk41
    quotient4Chunk42 quotient4Chunk43
    quotient4Chunk44 quotient4Chunk45
    quotient4Chunk46 quotient4Chunk47
    term
  compute_degree

private lemma quotient4Block4_degree : quotient4Block4.natDegree ≤ 1 := by
  unfold quotient4Block4 quotient4Chunk48 quotient4Chunk49
    quotient4Chunk50 quotient4Chunk51
    quotient4Chunk52 quotient4Chunk53
    quotient4Chunk54 quotient4Chunk55
    quotient4Chunk56 quotient4Chunk57
    quotient4Chunk58 quotient4Chunk59
    term
  compute_degree
  norm_num

private lemma quotient4Block5_degree : quotient4Block5.natDegree ≤ 1 := by
  unfold quotient4Block5 quotient4Chunk60 quotient4Chunk61
    quotient4Chunk62 quotient4Chunk63
    quotient4Chunk64 quotient4Chunk65
    quotient4Chunk66 quotient4Chunk67
    quotient4Chunk68 quotient4Chunk69
    quotient4Chunk70 quotient4Chunk71
    term
  compute_degree
  norm_num

private lemma quotient4Block6_degree : quotient4Block6.natDegree ≤ 1 := by
  unfold quotient4Block6 quotient4Chunk72 quotient4Chunk73
    quotient4Chunk74 quotient4Chunk75
    quotient4Chunk76 quotient4Chunk77
    quotient4Chunk78 quotient4Chunk79
    quotient4Chunk80 quotient4Chunk81
    quotient4Chunk82 quotient4Chunk83
    term
  compute_degree
  norm_num

private lemma quotient4Block7_degree : quotient4Block7.natDegree ≤ 1 := by
  unfold quotient4Block7 quotient4Chunk84 quotient4Chunk85
    quotient4Chunk86 term
  compute_degree
  norm_num

private lemma quotient4_degree : quotient4.natDegree ≤ 1 := by
  unfold quotient4
  apply natDegree_add_le_of_le
  · apply natDegree_add_le_of_le
    · apply natDegree_add_le_of_le
      · apply natDegree_add_le_of_le
        · apply natDegree_add_le_of_le
          · apply natDegree_add_le_of_le
            · apply natDegree_add_le_of_le
              · exact quotient4Block0_degree
              · exact quotient4Block1_degree
            · exact quotient4Block2_degree
          · exact quotient4Block3_degree
        · exact quotient4Block4_degree
      · exact quotient4Block5_degree
    · exact quotient4Block6_degree
  · exact quotient4Block7_degree

private lemma quotient5Block0_degree : quotient5Block0.natDegree ≤ 1 := by
  unfold quotient5Block0 quotient5Chunk0 quotient5Chunk1
    quotient5Chunk2 quotient5Chunk3
    quotient5Chunk4 quotient5Chunk5
    quotient5Chunk6 quotient5Chunk7
    quotient5Chunk8 quotient5Chunk9
    quotient5Chunk10 quotient5Chunk11
    term
  compute_degree

private lemma quotient5Block1_degree : quotient5Block1.natDegree ≤ 1 := by
  unfold quotient5Block1 quotient5Chunk12 quotient5Chunk13
    quotient5Chunk14 quotient5Chunk15
    quotient5Chunk16 quotient5Chunk17
    quotient5Chunk18 quotient5Chunk19
    quotient5Chunk20 quotient5Chunk21
    quotient5Chunk22 quotient5Chunk23
    term
  compute_degree

private lemma quotient5Block2_degree : quotient5Block2.natDegree ≤ 1 := by
  unfold quotient5Block2 quotient5Chunk24 quotient5Chunk25
    quotient5Chunk26 quotient5Chunk27
    quotient5Chunk28 quotient5Chunk29
    quotient5Chunk30 quotient5Chunk31
    quotient5Chunk32 quotient5Chunk33
    quotient5Chunk34 quotient5Chunk35
    term
  compute_degree

private lemma quotient5Block3_degree : quotient5Block3.natDegree ≤ 1 := by
  unfold quotient5Block3 quotient5Chunk36 quotient5Chunk37
    quotient5Chunk38 quotient5Chunk39
    quotient5Chunk40 quotient5Chunk41
    quotient5Chunk42 quotient5Chunk43
    quotient5Chunk44 quotient5Chunk45
    quotient5Chunk46 quotient5Chunk47
    term
  compute_degree

private lemma quotient5Block4_degree : quotient5Block4.natDegree ≤ 1 := by
  unfold quotient5Block4 quotient5Chunk48 quotient5Chunk49
    quotient5Chunk50 quotient5Chunk51
    quotient5Chunk52 quotient5Chunk53
    quotient5Chunk54 quotient5Chunk55
    quotient5Chunk56 quotient5Chunk57
    quotient5Chunk58 quotient5Chunk59
    term
  compute_degree
  norm_num

private lemma quotient5Block5_degree : quotient5Block5.natDegree ≤ 1 := by
  unfold quotient5Block5 quotient5Chunk60 quotient5Chunk61
    quotient5Chunk62 quotient5Chunk63
    quotient5Chunk64 quotient5Chunk65
    quotient5Chunk66 quotient5Chunk67
    quotient5Chunk68 quotient5Chunk69
    quotient5Chunk70 quotient5Chunk71
    term
  compute_degree
  norm_num

private lemma quotient5Block6_degree : quotient5Block6.natDegree ≤ 1 := by
  unfold quotient5Block6 quotient5Chunk72 quotient5Chunk73
    quotient5Chunk74 quotient5Chunk75
    quotient5Chunk76 quotient5Chunk77
    term
  compute_degree
  norm_num

private lemma quotient5_degree : quotient5.natDegree ≤ 1 := by
  unfold quotient5
  apply natDegree_add_le_of_le
  · apply natDegree_add_le_of_le
    · apply natDegree_add_le_of_le
      · apply natDegree_add_le_of_le
        · apply natDegree_add_le_of_le
          · apply natDegree_add_le_of_le
            · exact quotient5Block0_degree
            · exact quotient5Block1_degree
          · exact quotient5Block2_degree
        · exact quotient5Block3_degree
      · exact quotient5Block4_degree
    · exact quotient5Block5_degree
  · exact quotient5Block6_degree

private lemma quotient6Block0_degree : quotient6Block0.natDegree ≤ 1 := by
  unfold quotient6Block0 quotient6Chunk0 quotient6Chunk1
    quotient6Chunk2 quotient6Chunk3
    quotient6Chunk4 quotient6Chunk5
    quotient6Chunk6 quotient6Chunk7
    quotient6Chunk8 quotient6Chunk9
    quotient6Chunk10 quotient6Chunk11
    term
  compute_degree

private lemma quotient6Block1_degree : quotient6Block1.natDegree ≤ 1 := by
  unfold quotient6Block1 quotient6Chunk12 quotient6Chunk13
    quotient6Chunk14 quotient6Chunk15
    quotient6Chunk16 quotient6Chunk17
    quotient6Chunk18 quotient6Chunk19
    quotient6Chunk20 quotient6Chunk21
    quotient6Chunk22 quotient6Chunk23
    term
  compute_degree

private lemma quotient6Block2_degree : quotient6Block2.natDegree ≤ 1 := by
  unfold quotient6Block2 quotient6Chunk24 quotient6Chunk25
    quotient6Chunk26 quotient6Chunk27
    quotient6Chunk28 quotient6Chunk29
    quotient6Chunk30 quotient6Chunk31
    quotient6Chunk32 quotient6Chunk33
    quotient6Chunk34 quotient6Chunk35
    term
  compute_degree

private lemma quotient6Block3_degree : quotient6Block3.natDegree ≤ 1 := by
  unfold quotient6Block3 quotient6Chunk36 quotient6Chunk37
    quotient6Chunk38 quotient6Chunk39
    quotient6Chunk40 quotient6Chunk41
    quotient6Chunk42 quotient6Chunk43
    quotient6Chunk44 quotient6Chunk45
    quotient6Chunk46 quotient6Chunk47
    term
  compute_degree
  norm_num

private lemma quotient6Block4_degree : quotient6Block4.natDegree ≤ 1 := by
  unfold quotient6Block4 quotient6Chunk48 quotient6Chunk49
    quotient6Chunk50 quotient6Chunk51
    quotient6Chunk52 quotient6Chunk53
    quotient6Chunk54 quotient6Chunk55
    quotient6Chunk56 quotient6Chunk57
    term
  compute_degree
  norm_num

private lemma quotient6_degree : quotient6.natDegree ≤ 1 := by
  unfold quotient6
  apply natDegree_add_le_of_le
  · apply natDegree_add_le_of_le
    · apply natDegree_add_le_of_le
      · apply natDegree_add_le_of_le
        · exact quotient6Block0_degree
        · exact quotient6Block1_degree
      · exact quotient6Block2_degree
    · exact quotient6Block3_degree
  · exact quotient6Block4_degree

private lemma remainder1_coeff_seven : remainder1.coeff 7 = 1 := by
  simp [remainder1]

private lemma remainder2Block0_bicoeff :
    (remainder2Block0.coeff 6).coeff 0 =
      (-((606 : ℚ))) := by
  norm_num [remainder2Block0, remainder2Chunk0, remainder2Chunk1,
    remainder2Chunk2, remainder2Chunk3,
    remainder2Chunk4, remainder2Chunk5,
    remainder2Chunk6, remainder2Chunk7,
    remainder2Chunk8, remainder2Chunk9,
    remainder2Chunk10, remainder2Chunk11,
    term, Polynomial.coeff_monomial]

private lemma remainder2Block1_bicoeff :
    (remainder2Block1.coeff 6).coeff 0 =
      (0 : ℚ) := by
  norm_num [remainder2Block1, remainder2Chunk12, remainder2Chunk13,
    remainder2Chunk14, remainder2Chunk15,
    remainder2Chunk16, remainder2Chunk17,
    remainder2Chunk18, remainder2Chunk19,
    remainder2Chunk20, remainder2Chunk21,
    remainder2Chunk22, remainder2Chunk23,
    term, Polynomial.coeff_monomial]

private lemma remainder2Block2_bicoeff :
    (remainder2Block2.coeff 6).coeff 0 =
      (0 : ℚ) := by
  norm_num [remainder2Block2, remainder2Chunk24, remainder2Chunk25,
    remainder2Chunk26, remainder2Chunk27,
    remainder2Chunk28, remainder2Chunk29,
    remainder2Chunk30, remainder2Chunk31,
    remainder2Chunk32, remainder2Chunk33,
    remainder2Chunk34, remainder2Chunk35,
    term, Polynomial.coeff_monomial]

private lemma remainder2Block3_bicoeff :
    (remainder2Block3.coeff 6).coeff 0 =
      (0 : ℚ) := by
  norm_num [remainder2Block3, remainder2Chunk36, remainder2Chunk37,
    remainder2Chunk38, remainder2Chunk39,
    remainder2Chunk40, remainder2Chunk41,
    remainder2Chunk42, remainder2Chunk43,
    remainder2Chunk44, remainder2Chunk45,
    remainder2Chunk46, remainder2Chunk47,
    term, Polynomial.coeff_monomial]

private lemma remainder2Block4_bicoeff :
    (remainder2Block4.coeff 6).coeff 0 =
      (0 : ℚ) := by
  norm_num [remainder2Block4, remainder2Chunk48, remainder2Chunk49,
    remainder2Chunk50, remainder2Chunk51,
    remainder2Chunk52, remainder2Chunk53,
    remainder2Chunk54, remainder2Chunk55,
    remainder2Chunk56, remainder2Chunk57,
    remainder2Chunk58, remainder2Chunk59,
    term, Polynomial.coeff_monomial]

private lemma remainder2Block5_bicoeff :
    (remainder2Block5.coeff 6).coeff 0 =
      (0 : ℚ) := by
  norm_num [remainder2Block5, remainder2Chunk60, remainder2Chunk61,
    remainder2Chunk62, remainder2Chunk63,
    remainder2Chunk64, remainder2Chunk65,
    remainder2Chunk66, remainder2Chunk67,
    remainder2Chunk68, remainder2Chunk69,
    remainder2Chunk70, remainder2Chunk71,
    term, Polynomial.coeff_monomial]

private lemma remainder2Block6_bicoeff :
    (remainder2Block6.coeff 6).coeff 0 =
      (0 : ℚ) := by
  norm_num [remainder2Block6, remainder2Chunk72, remainder2Chunk73,
    remainder2Chunk74, remainder2Chunk75,
    remainder2Chunk76, remainder2Chunk77,
    remainder2Chunk78, remainder2Chunk79,
    remainder2Chunk80, remainder2Chunk81,
    remainder2Chunk82, remainder2Chunk83,
    term, Polynomial.coeff_monomial]

private lemma remainder2Block7_bicoeff :
    (remainder2Block7.coeff 6).coeff 0 =
      (0 : ℚ) := by
  norm_num [remainder2Block7, remainder2Chunk84, remainder2Chunk85,
    remainder2Chunk86, remainder2Chunk87,
    remainder2Chunk88, remainder2Chunk89,
    remainder2Chunk90, remainder2Chunk91,
    remainder2Chunk92, term,
    Polynomial.coeff_monomial]

private lemma remainder2_leadingCoeff_ne_zero :
    remainder2.coeff 6 ≠ 0 := by
  intro h
  have h0 := congrArg (fun p : Coefficient ↦ p.coeff 0) h
  norm_num [remainder2, remainder2Block0_bicoeff, remainder2Block1_bicoeff,
    remainder2Block2_bicoeff, remainder2Block3_bicoeff,
    remainder2Block4_bicoeff, remainder2Block5_bicoeff,
    remainder2Block6_bicoeff, remainder2Block7_bicoeff] at h0

private lemma remainder3Block0_bicoeff :
    (remainder3Block0.coeff 5).coeff 0 =
      (0 : ℚ) := by
  norm_num [remainder3Block0, remainder3Chunk0, remainder3Chunk1,
    remainder3Chunk2, remainder3Chunk3,
    remainder3Chunk4, remainder3Chunk5,
    remainder3Chunk6, remainder3Chunk7,
    remainder3Chunk8, remainder3Chunk9,
    remainder3Chunk10, remainder3Chunk11,
    term, Polynomial.coeff_monomial]

private lemma remainder3Block1_bicoeff :
    (remainder3Block1.coeff 5).coeff 0 =
      (64 : ℚ) := by
  norm_num [remainder3Block1, remainder3Chunk12, remainder3Chunk13,
    remainder3Chunk14, remainder3Chunk15,
    remainder3Chunk16, remainder3Chunk17,
    remainder3Chunk18, remainder3Chunk19,
    remainder3Chunk20, remainder3Chunk21,
    remainder3Chunk22, remainder3Chunk23,
    term, Polynomial.coeff_monomial]

private lemma remainder3Block2_bicoeff :
    (remainder3Block2.coeff 5).coeff 0 =
      (0 : ℚ) := by
  norm_num [remainder3Block2, remainder3Chunk24, remainder3Chunk25,
    remainder3Chunk26, remainder3Chunk27,
    remainder3Chunk28, remainder3Chunk29,
    remainder3Chunk30, remainder3Chunk31,
    remainder3Chunk32, remainder3Chunk33,
    remainder3Chunk34, remainder3Chunk35,
    term, Polynomial.coeff_monomial]

private lemma remainder3Block3_bicoeff :
    (remainder3Block3.coeff 5).coeff 0 =
      (0 : ℚ) := by
  norm_num [remainder3Block3, remainder3Chunk36, remainder3Chunk37,
    remainder3Chunk38, remainder3Chunk39,
    remainder3Chunk40, remainder3Chunk41,
    remainder3Chunk42, remainder3Chunk43,
    remainder3Chunk44, remainder3Chunk45,
    remainder3Chunk46, remainder3Chunk47,
    term, Polynomial.coeff_monomial]

private lemma remainder3Block4_bicoeff :
    (remainder3Block4.coeff 5).coeff 0 =
      (0 : ℚ) := by
  norm_num [remainder3Block4, remainder3Chunk48, remainder3Chunk49,
    remainder3Chunk50, remainder3Chunk51,
    remainder3Chunk52, remainder3Chunk53,
    remainder3Chunk54, remainder3Chunk55,
    remainder3Chunk56, remainder3Chunk57,
    remainder3Chunk58, remainder3Chunk59,
    term, Polynomial.coeff_monomial]

private lemma remainder3Block5_bicoeff :
    (remainder3Block5.coeff 5).coeff 0 =
      (0 : ℚ) := by
  norm_num [remainder3Block5, remainder3Chunk60, remainder3Chunk61,
    remainder3Chunk62, remainder3Chunk63,
    remainder3Chunk64, remainder3Chunk65,
    remainder3Chunk66, remainder3Chunk67,
    remainder3Chunk68, remainder3Chunk69,
    remainder3Chunk70, remainder3Chunk71,
    term, Polynomial.coeff_monomial]

private lemma remainder3Block6_bicoeff :
    (remainder3Block6.coeff 5).coeff 0 =
      (0 : ℚ) := by
  norm_num [remainder3Block6, remainder3Chunk72, remainder3Chunk73,
    remainder3Chunk74, remainder3Chunk75,
    remainder3Chunk76, remainder3Chunk77,
    remainder3Chunk78, remainder3Chunk79,
    remainder3Chunk80, remainder3Chunk81,
    remainder3Chunk82, remainder3Chunk83,
    term, Polynomial.coeff_monomial]

private lemma remainder3Block7_bicoeff :
    (remainder3Block7.coeff 5).coeff 0 =
      (0 : ℚ) := by
  norm_num [remainder3Block7, remainder3Chunk84, remainder3Chunk85,
    remainder3Chunk86, remainder3Chunk87,
    remainder3Chunk88, remainder3Chunk89,
    remainder3Chunk90, remainder3Chunk91,
    remainder3Chunk92, remainder3Chunk93,
    remainder3Chunk94, remainder3Chunk95,
    term, Polynomial.coeff_monomial]

private lemma remainder3Block8_bicoeff :
    (remainder3Block8.coeff 5).coeff 0 =
      (0 : ℚ) := by
  norm_num [remainder3Block8, remainder3Chunk96, remainder3Chunk97,
    remainder3Chunk98, remainder3Chunk99,
    remainder3Chunk100, remainder3Chunk101,
    remainder3Chunk102, remainder3Chunk103,
    remainder3Chunk104, remainder3Chunk105,
    remainder3Chunk106, remainder3Chunk107,
    term, Polynomial.coeff_monomial]

private lemma remainder3_leadingCoeff_ne_zero :
    remainder3.coeff 5 ≠ 0 := by
  intro h
  have h0 := congrArg (fun p : Coefficient ↦ p.coeff 0) h
  norm_num [remainder3, remainder3Block0_bicoeff, remainder3Block1_bicoeff,
    remainder3Block2_bicoeff, remainder3Block3_bicoeff,
    remainder3Block4_bicoeff, remainder3Block5_bicoeff,
    remainder3Block6_bicoeff, remainder3Block7_bicoeff,
    remainder3Block8_bicoeff] at h0

private lemma remainder4Block0_bicoeff :
    (remainder4Block0.coeff 4).coeff 0 =
      (0 : ℚ) := by
  norm_num [remainder4Block0, remainder4Chunk0, remainder4Chunk1,
    remainder4Chunk2, remainder4Chunk3,
    remainder4Chunk4, remainder4Chunk5,
    remainder4Chunk6, remainder4Chunk7,
    remainder4Chunk8, remainder4Chunk9,
    remainder4Chunk10, remainder4Chunk11,
    term, Polynomial.coeff_monomial]

private lemma remainder4Block1_bicoeff :
    (remainder4Block1.coeff 4).coeff 0 =
      (-((384736 : ℚ))) := by
  norm_num [remainder4Block1, remainder4Chunk12, remainder4Chunk13,
    remainder4Chunk14, remainder4Chunk15,
    remainder4Chunk16, remainder4Chunk17,
    remainder4Chunk18, remainder4Chunk19,
    remainder4Chunk20, remainder4Chunk21,
    remainder4Chunk22, remainder4Chunk23,
    term, Polynomial.coeff_monomial]

private lemma remainder4Block2_bicoeff :
    (remainder4Block2.coeff 4).coeff 0 =
      (0 : ℚ) := by
  norm_num [remainder4Block2, remainder4Chunk24, remainder4Chunk25,
    remainder4Chunk26, remainder4Chunk27,
    remainder4Chunk28, remainder4Chunk29,
    remainder4Chunk30, remainder4Chunk31,
    remainder4Chunk32, remainder4Chunk33,
    remainder4Chunk34, remainder4Chunk35,
    term, Polynomial.coeff_monomial]

private lemma remainder4Block3_bicoeff :
    (remainder4Block3.coeff 4).coeff 0 =
      (0 : ℚ) := by
  norm_num [remainder4Block3, remainder4Chunk36, remainder4Chunk37,
    remainder4Chunk38, remainder4Chunk39,
    remainder4Chunk40, remainder4Chunk41,
    remainder4Chunk42, remainder4Chunk43,
    remainder4Chunk44, remainder4Chunk45,
    remainder4Chunk46, remainder4Chunk47,
    term, Polynomial.coeff_monomial]

private lemma remainder4Block4_bicoeff :
    (remainder4Block4.coeff 4).coeff 0 =
      (0 : ℚ) := by
  norm_num [remainder4Block4, remainder4Chunk48, remainder4Chunk49,
    remainder4Chunk50, remainder4Chunk51,
    remainder4Chunk52, remainder4Chunk53,
    remainder4Chunk54, remainder4Chunk55,
    remainder4Chunk56, remainder4Chunk57,
    remainder4Chunk58, remainder4Chunk59,
    term, Polynomial.coeff_monomial]

private lemma remainder4Block5_bicoeff :
    (remainder4Block5.coeff 4).coeff 0 =
      (0 : ℚ) := by
  norm_num [remainder4Block5, remainder4Chunk60, remainder4Chunk61,
    remainder4Chunk62, remainder4Chunk63,
    remainder4Chunk64, remainder4Chunk65,
    remainder4Chunk66, remainder4Chunk67,
    remainder4Chunk68, remainder4Chunk69,
    remainder4Chunk70, remainder4Chunk71,
    term, Polynomial.coeff_monomial]

private lemma remainder4Block6_bicoeff :
    (remainder4Block6.coeff 4).coeff 0 =
      (0 : ℚ) := by
  norm_num [remainder4Block6, remainder4Chunk72, remainder4Chunk73,
    remainder4Chunk74, remainder4Chunk75,
    remainder4Chunk76, remainder4Chunk77,
    remainder4Chunk78, remainder4Chunk79,
    remainder4Chunk80, remainder4Chunk81,
    remainder4Chunk82, remainder4Chunk83,
    term, Polynomial.coeff_monomial]

private lemma remainder4Block7_bicoeff :
    (remainder4Block7.coeff 4).coeff 0 =
      (0 : ℚ) := by
  norm_num [remainder4Block7, remainder4Chunk84, remainder4Chunk85,
    remainder4Chunk86, remainder4Chunk87,
    remainder4Chunk88, remainder4Chunk89,
    remainder4Chunk90, remainder4Chunk91,
    remainder4Chunk92, remainder4Chunk93,
    remainder4Chunk94, remainder4Chunk95,
    term, Polynomial.coeff_monomial]

private lemma remainder4Block8_bicoeff :
    (remainder4Block8.coeff 4).coeff 0 =
      (0 : ℚ) := by
  norm_num [remainder4Block8, remainder4Chunk96, remainder4Chunk97,
    remainder4Chunk98, remainder4Chunk99,
    remainder4Chunk100, remainder4Chunk101,
    remainder4Chunk102, remainder4Chunk103,
    remainder4Chunk104, remainder4Chunk105,
    remainder4Chunk106, remainder4Chunk107,
    term, Polynomial.coeff_monomial]

private lemma remainder4Block9_bicoeff :
    (remainder4Block9.coeff 4).coeff 0 =
      (0 : ℚ) := by
  norm_num [remainder4Block9, remainder4Chunk108, remainder4Chunk109,
    remainder4Chunk110, remainder4Chunk111,
    remainder4Chunk112, remainder4Chunk113,
    remainder4Chunk114, remainder4Chunk115,
    remainder4Chunk116, term,
    Polynomial.coeff_monomial]

private lemma remainder4_leadingCoeff_ne_zero :
    remainder4.coeff 4 ≠ 0 := by
  intro h
  have h0 := congrArg (fun p : Coefficient ↦ p.coeff 0) h
  norm_num [remainder4, remainder4Block0_bicoeff, remainder4Block1_bicoeff,
    remainder4Block2_bicoeff, remainder4Block3_bicoeff,
    remainder4Block4_bicoeff, remainder4Block5_bicoeff,
    remainder4Block6_bicoeff, remainder4Block7_bicoeff,
    remainder4Block8_bicoeff, remainder4Block9_bicoeff] at h0

private lemma remainder5Block0_bicoeff :
    (remainder5Block0.coeff 3).coeff 0 =
      (0 : ℚ) := by
  norm_num [remainder5Block0, remainder5Chunk0, remainder5Chunk1,
    remainder5Chunk2, remainder5Chunk3,
    remainder5Chunk4, remainder5Chunk5,
    remainder5Chunk6, remainder5Chunk7,
    remainder5Chunk8, remainder5Chunk9,
    remainder5Chunk10, remainder5Chunk11,
    term, Polynomial.coeff_monomial]

private lemma remainder5Block1_bicoeff :
    (remainder5Block1.coeff 3).coeff 0 =
      (44628871650183547488 : ℚ) := by
  norm_num [remainder5Block1, remainder5Chunk12, remainder5Chunk13,
    remainder5Chunk14, remainder5Chunk15,
    remainder5Chunk16, remainder5Chunk17,
    remainder5Chunk18, remainder5Chunk19,
    remainder5Chunk20, remainder5Chunk21,
    remainder5Chunk22, remainder5Chunk23,
    term, Polynomial.coeff_monomial]

private lemma remainder5Block2_bicoeff :
    (remainder5Block2.coeff 3).coeff 0 =
      (0 : ℚ) := by
  norm_num [remainder5Block2, remainder5Chunk24, remainder5Chunk25,
    remainder5Chunk26, remainder5Chunk27,
    remainder5Chunk28, remainder5Chunk29,
    remainder5Chunk30, remainder5Chunk31,
    remainder5Chunk32, remainder5Chunk33,
    remainder5Chunk34, remainder5Chunk35,
    term, Polynomial.coeff_monomial]

private lemma remainder5Block3_bicoeff :
    (remainder5Block3.coeff 3).coeff 0 =
      (0 : ℚ) := by
  norm_num [remainder5Block3, remainder5Chunk36, remainder5Chunk37,
    remainder5Chunk38, remainder5Chunk39,
    remainder5Chunk40, remainder5Chunk41,
    remainder5Chunk42, remainder5Chunk43,
    remainder5Chunk44, remainder5Chunk45,
    remainder5Chunk46, remainder5Chunk47,
    term, Polynomial.coeff_monomial]

private lemma remainder5Block4_bicoeff :
    (remainder5Block4.coeff 3).coeff 0 =
      (0 : ℚ) := by
  norm_num [remainder5Block4, remainder5Chunk48, remainder5Chunk49,
    remainder5Chunk50, remainder5Chunk51,
    remainder5Chunk52, remainder5Chunk53,
    remainder5Chunk54, remainder5Chunk55,
    remainder5Chunk56, remainder5Chunk57,
    remainder5Chunk58, remainder5Chunk59,
    term, Polynomial.coeff_monomial]

private lemma remainder5Block5_bicoeff :
    (remainder5Block5.coeff 3).coeff 0 =
      (0 : ℚ) := by
  norm_num [remainder5Block5, remainder5Chunk60, remainder5Chunk61,
    remainder5Chunk62, remainder5Chunk63,
    remainder5Chunk64, remainder5Chunk65,
    remainder5Chunk66, remainder5Chunk67,
    remainder5Chunk68, remainder5Chunk69,
    remainder5Chunk70, remainder5Chunk71,
    term, Polynomial.coeff_monomial]

private lemma remainder5Block6_bicoeff :
    (remainder5Block6.coeff 3).coeff 0 =
      (0 : ℚ) := by
  norm_num [remainder5Block6, remainder5Chunk72, remainder5Chunk73,
    remainder5Chunk74, remainder5Chunk75,
    remainder5Chunk76, remainder5Chunk77,
    remainder5Chunk78, remainder5Chunk79,
    remainder5Chunk80, remainder5Chunk81,
    remainder5Chunk82, remainder5Chunk83,
    term, Polynomial.coeff_monomial]

private lemma remainder5Block7_bicoeff :
    (remainder5Block7.coeff 3).coeff 0 =
      (0 : ℚ) := by
  norm_num [remainder5Block7, remainder5Chunk84, remainder5Chunk85,
    term, Polynomial.coeff_monomial]

private lemma remainder5_leadingCoeff_ne_zero :
    remainder5.coeff 3 ≠ 0 := by
  intro h
  have h0 := congrArg (fun p : Coefficient ↦ p.coeff 0) h
  norm_num [remainder5, remainder5Block0_bicoeff, remainder5Block1_bicoeff,
    remainder5Block2_bicoeff, remainder5Block3_bicoeff,
    remainder5Block4_bicoeff, remainder5Block5_bicoeff,
    remainder5Block6_bicoeff, remainder5Block7_bicoeff] at h0

private lemma remainder6Block0_bicoeff :
    (remainder6Block0.coeff 2).coeff 0 =
      (0 : ℚ) := by
  norm_num [remainder6Block0, remainder6Chunk0, remainder6Chunk1,
    remainder6Chunk2, remainder6Chunk3,
    remainder6Chunk4, remainder6Chunk5,
    remainder6Chunk6, remainder6Chunk7,
    remainder6Chunk8, remainder6Chunk9,
    remainder6Chunk10, remainder6Chunk11,
    term, Polynomial.coeff_monomial]

private lemma remainder6Block1_bicoeff :
    (remainder6Block1.coeff 2).coeff 0 =
      ((10878351506404408 : ℚ) * 10 ^ 36 +
        088424943674109583579961283044613696) := by
  norm_num [remainder6Block1, remainder6Chunk12, remainder6Chunk13,
    remainder6Chunk14, remainder6Chunk15,
    remainder6Chunk16, remainder6Chunk17,
    remainder6Chunk18, remainder6Chunk19,
    remainder6Chunk20, remainder6Chunk21,
    remainder6Chunk22, remainder6Chunk23,
    term, Polynomial.coeff_monomial]

private lemma remainder6Block2_bicoeff :
    (remainder6Block2.coeff 2).coeff 0 =
      (0 : ℚ) := by
  norm_num [remainder6Block2, remainder6Chunk24, remainder6Chunk25,
    remainder6Chunk26, remainder6Chunk27,
    remainder6Chunk28, remainder6Chunk29,
    remainder6Chunk30, remainder6Chunk31,
    remainder6Chunk32, remainder6Chunk33,
    remainder6Chunk34, remainder6Chunk35,
    term, Polynomial.coeff_monomial]

private lemma remainder6Block3_bicoeff :
    (remainder6Block3.coeff 2).coeff 0 =
      (0 : ℚ) := by
  norm_num [remainder6Block3, remainder6Chunk36, remainder6Chunk37,
    remainder6Chunk38, remainder6Chunk39,
    remainder6Chunk40, remainder6Chunk41,
    remainder6Chunk42, remainder6Chunk43,
    remainder6Chunk44, remainder6Chunk45,
    remainder6Chunk46, remainder6Chunk47,
    term, Polynomial.coeff_monomial]

private lemma remainder6Block4_bicoeff :
    (remainder6Block4.coeff 2).coeff 0 =
      (0 : ℚ) := by
  norm_num [remainder6Block4, remainder6Chunk48, remainder6Chunk49,
    remainder6Chunk50, remainder6Chunk51,
    remainder6Chunk52, remainder6Chunk53,
    remainder6Chunk54, remainder6Chunk55,
    term, Polynomial.coeff_monomial]

private lemma remainder6_leadingCoeff_ne_zero :
    remainder6.coeff 2 ≠ 0 := by
  intro h
  have h0 := congrArg (fun p : Coefficient ↦ p.coeff 0) h
  norm_num [remainder6, remainder6Block0_bicoeff, remainder6Block1_bicoeff,
    remainder6Block2_bicoeff, remainder6Block3_bicoeff,
    remainder6Block4_bicoeff] at h0

private lemma remainder7Block0_bicoeff :
    (remainder7Block0.coeff 1).coeff 0 =
      (-(((((10936686274920016753944339946648261 : ℚ) * 10 ^ 36 +
        311079539506766061191370316978138601) * 10 ^ 36 +
        651937247124165649252180932748749814) * 10 ^ 36 +
        996500235207123991788709041477672200))) := by
  norm_num [remainder7Block0, remainder7Chunk0, remainder7Chunk1,
    remainder7Chunk2, remainder7Chunk3,
    remainder7Chunk4, remainder7Chunk5,
    remainder7Chunk6, remainder7Chunk7,
    remainder7Chunk8, remainder7Chunk9,
    remainder7Chunk10, remainder7Chunk11,
    term, Polynomial.coeff_monomial]

private lemma remainder7Block1_bicoeff :
    (remainder7Block1.coeff 1).coeff 0 =
      (0 : ℚ) := by
  norm_num [remainder7Block1, remainder7Chunk12, remainder7Chunk13,
    remainder7Chunk14, remainder7Chunk15,
    remainder7Chunk16, remainder7Chunk17,
    remainder7Chunk18, remainder7Chunk19,
    remainder7Chunk20, remainder7Chunk21,
    term, Polynomial.coeff_monomial]

private lemma remainder7_leadingCoeff_ne_zero :
    remainder7.coeff 1 ≠ 0 := by
  intro h
  have h0 := congrArg (fun p : Coefficient ↦ p.coeff 0) h
  norm_num [remainder7, remainder7Block0_bicoeff, remainder7Block1_bicoeff] at h0

private lemma remainder8_eq : remainder8 = C (-1) := by
  norm_num [remainder8, remainder8Block0,
    remainder8Chunk0, term]

private theorem cmSix_eq_resultantFactorSix :
    cmSix = resultantFactorSix.map (Int.castRingHom ℚ) := by
  simp [cmSix, resultantFactorSix, parameter]

private theorem cmTwelve_eq_resultantFactorTwelve :
    cmTwelve = resultantFactorTwelve.map (Int.castRingHom ℚ) := by
  simp [cmTwelve, resultantFactorTwelve, parameter]

private theorem exceptional_monomial_identity
    {M : Type} [CommMonoid M]
    (a b q c6 c12 u3 u4 u5 u6 : M)
    (hunit : u3 ^ 4 * u4 ^ 3 * u5 ^ 2 * u6 = 1) :
    ((b ^ 6 * a ^ 7) ^ 7) * (q ^ 21) ^ 6 *
      (b * a ^ 2) ^ 5 * (u3 * q ^ 22) ^ 4 *
      (u4 * b * q ^ 4) ^ 3 * (u5 * a ^ 2 * q ^ 14 * c6) ^ 2 *
      (u6 * b * q ^ 6 * c12) =
        a ^ 63 * b ^ 51 * q ^ 260 * c6 ^ 2 * c12 := by
  have ha : a ^ 63 = a ^ 49 * a ^ 10 * a ^ 4 := by
    rw [show 63 = 49 + 10 + 4 by omega, pow_add, pow_add]
  have hb : b ^ 51 = b ^ 42 * b ^ 5 * b ^ 3 * b := by
    rw [show 51 = 42 + 5 + 3 + 1 by omega,
      pow_add, pow_add, pow_add, pow_one]
  have hq : q ^ 260 = q ^ 126 * q ^ 88 * q ^ 12 * q ^ 28 *
      q ^ 6 := by
    rw [show 260 = 126 + 88 + 12 + 28 + 6 by omega,
      pow_add, pow_add, pow_add, pow_add]
  calc
    _ = (u3 ^ 4 * u4 ^ 3 * u5 ^ 2 * u6) *
        (a ^ 49 * a ^ 10 * a ^ 4) *
        (b ^ 42 * b ^ 5 * b ^ 3 * b) *
        (q ^ 126 * q ^ 88 * q ^ 12 * q ^ 28 * q ^ 6) *
        c6 ^ 2 * c12 := by
      simp only [mul_pow]
      repeat rw [← pow_mul]
      norm_num
      ac_rfl
    _ = _ := by rw [hunit, ha, hb, hq]; ac_rfl

private theorem factored_expression_eq_resultantFactorData :
    parameter ^ 63 * (parameter - 1) ^ 51 *
      discriminantFactor ^ 260 * cmSix ^ 2 * cmTwelve =
      resultantFactorData := by
  have hp : parameter = X := rfl
  have h8 : (8 : Coefficient) = C 8 := rfl
  have h5 : (5 : Coefficient) = C 5 := rfl
  have hd : discriminantFactor =
      X ^ 3 - C 8 * X ^ 2 + C 5 * X + 1 := by
    rw [discriminantFactor, hp, h8, h5]
  unfold resultantFactorData
  rw [← cmSix_eq_resultantFactorSix,
    ← cmTwelve_eq_resultantFactorTwelve, hp, hd]

private theorem exceptional_product_eq_resultantFactorData :
    exceptional0 ^ 7 * exceptional1 ^ 6 * exceptional2 ^ 5 *
      exceptional3 ^ 4 * exceptional4 ^ 3 * exceptional5 ^ 2 *
      exceptional6 = resultantFactorData := by
  have hunit : exceptionalUnit3 ^ 4 * exceptionalUnit4 ^ 3 *
      exceptionalUnit5 ^ 2 * exceptionalUnit6 = 1 := by
    unfold exceptionalUnit3 exceptionalUnit4 exceptionalUnit5
      exceptionalUnit6
    rw [← map_pow, ← map_pow, ← map_pow,
      ← map_mul, ← map_mul, ← map_mul]
    norm_num
  have hmonomial := exceptional_monomial_identity
    parameter (parameter - 1) discriminantFactor cmSix cmTwelve
    exceptionalUnit3 exceptionalUnit4 exceptionalUnit5
    exceptionalUnit6 hunit
  rw [← factored_expression_eq_resultantFactorData, ← hmonomial]
  unfold exceptional0 exceptional1 exceptional2 exceptional3
    exceptional4 exceptional5 exceptional6
  simp only [exceptionalUnit0, exceptionalUnit1, exceptionalUnit2,
    map_one, one_mul, pow_one]

end Internal.ResultantCertificate

open Internal.ResultantCertificate

/-- The seven checked pseudo-remainder recurrences imply the exact
generic factorization of the first bounded resultant over `ℚ[D]`. -/
theorem generic_resultant_eq_resultantFactorData
    (hrec0 : recurrence0) (hrec1 : recurrence1)
    (hrec2 : recurrence2) (hrec3 : recurrence3)
    (hrec4 : recurrence4) (hrec5 : recurrence5)
    (hrec6 : recurrence6) :
    resultant selectionCofactorData divisionCofactorData0 33 7 =
      resultantFactorData := by
  have h := bounded_resultant_telescope_33_7
    remainder0 remainder1 remainder2 remainder3 remainder4
    remainder5 remainder6 remainder7 remainder8
    quotient0 quotient1 quotient2 quotient3 quotient4 quotient5 quotient6
    (remainder2.coeff 6) (remainder3.coeff 5)
    (remainder4.coeff 4) (remainder5.coeff 3)
    (remainder6.coeff 2) (remainder7.coeff 1)
    exceptional0 exceptional1 exceptional2 exceptional3
    exceptional4 exceptional5 exceptional6 (-1)
    remainder1_degree remainder2_degree remainder3_degree
    remainder4_degree remainder5_degree remainder6_degree
    remainder7_degree remainder8_degree
    (by have := quotient0_degree; omega)
    (by have := quotient1_degree; omega)
    (by have := quotient2_degree; omega)
    (by have := quotient3_degree; omega)
    (by have := quotient4_degree; omega)
    (by have := quotient5_degree; omega)
    (by have := quotient6_degree; omega)
    remainder1_coeff_seven rfl rfl rfl rfl rfl rfl
    remainder2_leadingCoeff_ne_zero
    remainder3_leadingCoeff_ne_zero
    remainder4_leadingCoeff_ne_zero
    remainder5_leadingCoeff_ne_zero
    remainder6_leadingCoeff_ne_zero
    remainder7_leadingCoeff_ne_zero
    (by simpa only [recurrence0] using hrec0)
    (by simpa only [recurrence1] using hrec1)
    (by simpa only [recurrence2] using hrec2)
    (by simpa only [recurrence3] using hrec3)
    (by simpa only [recurrence4] using hrec4)
    (by simpa only [recurrence5] using hrec5)
    (by simpa only [recurrence6] using hrec6)
    remainder8_eq
  calc
    resultant selectionCofactorData divisionCofactorData0 33 7 =
        exceptional0 ^ 7 * exceptional1 ^ 6 * exceptional2 ^ 5 *
          exceptional3 ^ 4 * exceptional4 ^ 3 * exceptional5 ^ 2 *
          exceptional6 := by
      rw [← remainder0, ← remainder1]
      calc
        resultant remainder0 remainder1 33 7 =
            -exceptional0 ^ 7 * exceptional1 ^ 6 * exceptional2 ^ 5 *
              exceptional3 ^ 4 * exceptional4 ^ 3 * exceptional5 ^ 2 *
              exceptional6 * (-1) := h
        _ = exceptional0 ^ 7 * exceptional1 ^ 6 * exceptional2 ^ 5 *
              exceptional3 ^ 4 * exceptional4 ^ 3 * exceptional5 ^ 2 *
              exceptional6 := by ring
    _ = resultantFactorData := exceptional_product_eq_resultantFactorData

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
