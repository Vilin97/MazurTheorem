/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData4
import Mathlib.Tactic.NormNum

/-!
# Recurrence 4 lookup certificate: B1 source coefficients, low half

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence4B1_coeff_0 :
    remainder5Coefficient1.coeff 0 =
      (0 : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_1 :
    remainder5Coefficient1.coeff 1 =
      (260832740765859690536 : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_2 :
    remainder5Coefficient1.coeff 2 =
      (-599798859925772952688186 : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_3 :
    remainder5Coefficient1.coeff 3 =
      (515010438763430378824396622 : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_4 :
    remainder5Coefficient1.coeff 4 =
      (-76912847307884185746204152022 : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_5 :
    remainder5Coefficient1.coeff 5 =
      (-39528662864659869708437973812678 : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_6 :
    remainder5Coefficient1.coeff 6 =
      (22423278808863624534504605339183226 : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_7 :
    remainder5Coefficient1.coeff 7 =
      (1089539022471937695962046850508211745 : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_8 :
    remainder5Coefficient1.coeff 8 =
      (-5539138044347443264592969557290651346342 : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_9 :
    remainder5Coefficient1.coeff 9 =
      (2759182459620370707593704668275573321509342 : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_10 :
    remainder5Coefficient1.coeff 10 =
      (-747400383590690394016557379090120796900268778 : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_11 :
    remainder5Coefficient1.coeff 11 =
      (126612037565207748711252839349707309075819048058 : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_12 :
    remainder5Coefficient1.coeff 12 =
      (-12860469566166149164120902333488903484738828469792 : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_13 :
    remainder5Coefficient1.coeff 13 =
      (404418412191306202383123061756659703928354139879885 : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_14 :
    remainder5Coefficient1.coeff 14 =
      (107750878548261641043501687245211387141932508084083991 : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_15 :
    remainder5Coefficient1.coeff 15 =
      (-23166381876054735843275285873213589333475539084952971659 : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_16 :
    remainder5Coefficient1.coeff 16 =
      (2688529921402536393055733759606458252566391905484993603159 : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_17 :
    remainder5Coefficient1.coeff 17 =
      (-224171429964828927017100655951580555169129913077115092787821 : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_18 :
    remainder5Coefficient1.coeff 18 =
      (14566404178546139416758100729272237835136887482028211602144981 : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_19 :
    remainder5Coefficient1.coeff 19 =
      (-765722068558499201180134478315214402263190045596988877938205075 : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_20 :
    remainder5Coefficient1.coeff 20 =
      (33253152462493620736482618023761878117727901650417223642924796770 : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_21 :
    remainder5Coefficient1.coeff 21 =
      (-1207697414782672261991814930754965149898711722039585827325328614888 : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_22 :
    remainder5Coefficient1.coeff 22 =
      (36894752563148269340382387511433123990836885797389013633548790264222 : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_23 :
    remainder5Coefficient1.coeff 23 =
      (-946889771867600408490987391079160752275595124773646170957269967190265 : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_24 :
    remainder5Coefficient1.coeff 24 =
      ((2 * 10 ^ 70 +
        0158473225132267568099372506683966939613222119820016704611350742232622) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_25 :
    remainder5Coefficient1.coeff 25 =
      -((34 * 10 ^ 70 +
        2425635355046085094224113851230423708246451970946047611114168504570070) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_26 :
    remainder5Coefficient1.coeff 26 =
      ((407 * 10 ^ 70 +
        2966914225350199131521764868335241934997033198683544626147080883863034) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_27 :
    remainder5Coefficient1.coeff 27 =
      -((1073 * 10 ^ 70 +
        4137178338839485712271756532299302949713032291706874478304724376772173) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_28 :
    remainder5Coefficient1.coeff 28 =
      -((107800 * 10 ^ 70 +
        0822150445056023164343532454246889584875027742088150663327162512260997) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_29 :
    remainder5Coefficient1.coeff 29 =
      ((3841409 * 10 ^ 70 +
        0127400061991043226322678611284363736158020364771961742198172298435886) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_30 :
    remainder5Coefficient1.coeff 30 =
      -((88204154 * 10 ^ 70 +
        5277031475068952765368880376134639482003752248789748046311794563337986) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_31 :
    remainder5Coefficient1.coeff 31 =
      ((1624376868 * 10 ^ 70 +
        9274205282493336470461503415753298775876686096885081681426971485566054) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_32 :
    remainder5Coefficient1.coeff 32 =
      -((25612410183 * 10 ^ 70 +
        8609413040640021198707750544394788394553795502344981693366672515298724) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_33 :
    remainder5Coefficient1.coeff 33 =
      ((356230591766 * 10 ^ 70 +
        1329170384249737344716042195594487796638397433682672419481570058154464) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_34 :
    remainder5Coefficient1.coeff 34 =
      -((4445085026502 * 10 ^ 70 +
        0131513557458933692752871780838246964906310792875834306288393098836574) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_35 :
    remainder5Coefficient1.coeff 35 =
      ((50313218345640 * 10 ^ 70 +
        3169612861687876152407403211734562201205103934585558011710669101002613) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_36 :
    remainder5Coefficient1.coeff 36 =
      -((520664163330927 * 10 ^ 70 +
        8800692962456451470131845868029784506859201261348669540912263401122315) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_37 :
    remainder5Coefficient1.coeff 37 =
      ((4955864976207658 * 10 ^ 70 +
        8815247979212087498968122289188079145106302773575188546356153777684103) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_38 :
    remainder5Coefficient1.coeff 38 =
      -((43597444005474814 * 10 ^ 70 +
        7263746612908301238772220104262591674595095327302637059241243467470476) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_39 :
    remainder5Coefficient1.coeff 39 =
      ((355893318220401883 * 10 ^ 70 +
        7163127712136060469025333540172237070052394559799856379258362651353854) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_40 :
    remainder5Coefficient1.coeff 40 =
      -((2705050941619091308 * 10 ^ 70 +
        2110795204372530891369750778502519732436438563209689474061662518286595) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_41 :
    remainder5Coefficient1.coeff 41 =
      ((19200481117689800232 * 10 ^ 70 +
        4668342056095532238274417706144057471425387160163332738910171036444153) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_42 :
    remainder5Coefficient1.coeff 42 =
      -((127602872909224349786 * 10 ^ 70 +
        9027916509621896435233097878544966867450350838696907788334343998397699) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_43 :
    remainder5Coefficient1.coeff 43 =
      ((795841185785076740165 * 10 ^ 70 +
        9309173945927028272794101628623613643603091437016767625488751027851187) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_44 :
    remainder5Coefficient1.coeff 44 =
      -((4667797368998863559042 * 10 ^ 70 +
        0714201812552778422945165845372512322415198528862474212366226333448589) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_45 :
    remainder5Coefficient1.coeff 45 =
      ((25794710418122814887995 * 10 ^ 70 +
        4206068277389735340088939657367322612721668027982701572002143131173881) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_46 :
    remainder5Coefficient1.coeff 46 =
      -((134529957951725175415850 * 10 ^ 70 +
        7694084246620578150355531150212314546178526879133543930020982494219926) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_47 :
    remainder5Coefficient1.coeff 47 =
      ((663202243208303198526325 * 10 ^ 70 +
        9521270539713472251764250298244190751857845645230390853073436424114775) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_48 :
    remainder5Coefficient1.coeff 48 =
      -((3094712002575881337884174 * 10 ^ 70 +
        5002306532671953443516011954395699408791339283093914526076844646793612) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_49 :
    remainder5Coefficient1.coeff 49 =
      ((13686618786856234219723315 * 10 ^ 70 +
        8599816138809727317571813853001191393711101520666531130396927921262073) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_50 :
    remainder5Coefficient1.coeff 50 =
      -((57435321246250417877565368 * 10 ^ 70 +
        7460719276143192048655766796279689455667934253768308250671922172155502) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_51 :
    remainder5Coefficient1.coeff 51 =
      ((228944076478171014327903225 * 10 ^ 70 +
        2076153767400093530774958642662054428751749943706116246021682538798597) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_52 :
    remainder5Coefficient1.coeff 52 =
      -((867694494161462255265845676 * 10 ^ 70 +
        3606382991812857909026448457243261595585057927929636871343728258157446) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_53 :
    remainder5Coefficient1.coeff 53 =
      ((3129488911946689640468618177 * 10 ^ 70 +
        7818291972969409688734379246803722826318332304639390383296188373497996) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_54 :
    remainder5Coefficient1.coeff 54 =
      -((10749709307353405726762716903 * 10 ^ 70 +
        3365536188971723394128674540542921456842504585340615132630263373065458) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_55 :
    remainder5Coefficient1.coeff 55 =
      ((35192699711861319155000110771 * 10 ^ 70 +
        1037904887955372379142707270985603210853177172072853393838620378017565) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_56 :
    remainder5Coefficient1.coeff 56 =
      -((109882256146846934735222112234 * 10 ^ 70 +
        9495691637242789127257042836062309316848315626134489909779037896320075) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_57 :
    remainder5Coefficient1.coeff 57 =
      ((327401902230678581643222116579 * 10 ^ 70 +
        6185792676965783441327175243979437270619246487090808305435057920569657) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_58 :
    remainder5Coefficient1.coeff 58 =
      -((931425194070347587255716696523 * 10 ^ 70 +
        5877657872432593133714054016638145486911276485112104330236456965530760) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_59 :
    remainder5Coefficient1.coeff 59 =
      ((2531274248765978708787738179331 * 10 ^ 70 +
        8062082897426744081475736567353011692991460807645362675105244652854633) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_60 :
    remainder5Coefficient1.coeff 60 =
      -((6574224210245251490678681380417 * 10 ^ 70 +
        4077850819745080020207550473555282732712569579444717465936907310939783) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_61 :
    remainder5Coefficient1.coeff 61 =
      ((16324252803432586294735877047285 * 10 ^ 70 +
        4567351443877819205206286940715924185024883925610669479882835221655651) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_62 :
    remainder5Coefficient1.coeff 62 =
      -((38766439695288143246873265423796 * 10 ^ 70 +
        6661341681036478585522743700151877700915854619518719937291500761193633) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_63 :
    remainder5Coefficient1.coeff 63 =
      ((88073349567423609195841951843886 * 10 ^ 70 +
        9480306512099937629229735307258490759353328846412203271867716980014357) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_64 :
    remainder5Coefficient1.coeff 64 =
      -((191475800236824200576440103082636 * 10 ^ 70 +
        2768671618406765034722462103054454347224394111805903178374041819370269) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_65 :
    remainder5Coefficient1.coeff 65 =
      ((398439112484155484454543642408985 * 10 ^ 70 +
        5926369066589357910244045669887108952349869008025282308239974386602362) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_66 :
    remainder5Coefficient1.coeff 66 =
      -((793724917959088796271662148830966 * 10 ^ 70 +
        1040010171879851744342916069759079336552183625067516128368252079476487) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_67 :
    remainder5Coefficient1.coeff 67 =
      ((1513919274157322364974261659701795 * 10 ^ 70 +
        2638368444775011300095486686675917903890092706225413621571703147503639) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_68 :
    remainder5Coefficient1.coeff 68 =
      -((2765080906557860093968305786589136 * 10 ^ 70 +
        8005431794885430156686738237415682262568325843772676649259820542168183) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_69 :
    remainder5Coefficient1.coeff 69 =
      ((4836326705641471512964273717373941 * 10 ^ 70 +
        7399435002114797499621492445237287120868873848717277562153309748872497) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_70 :
    remainder5Coefficient1.coeff 70 =
      -((8100984003137201844308502178452100 * 10 ^ 70 +
        1201688770830957762093564716878437988898279448072883073675188576330695) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_71 :
    remainder5Coefficient1.coeff 71 =
      ((12994689989334740222107964620929393 * 10 ^ 70 +
        8986843356094522206051351167500757880829332701099353556922973040191525) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_72 :
    remainder5Coefficient1.coeff 72 =
      -((19960415658616801947711267355696551 * 10 ^ 70 +
        6618464674616421778582691312075227002277185448735786639161226919167657) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_73 :
    remainder5Coefficient1.coeff 73 =
      ((29355753946918704488511248595012026 * 10 ^ 70 +
        5071827747381710424814929060998090220837605529668388213985010020650927) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_74 :
    remainder5Coefficient1.coeff 74 =
      -((41328771065320954458440160990262688 * 10 ^ 70 +
        8784001651799251341035120097729985619761423225828734123153002700954741) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_75 :
    remainder5Coefficient1.coeff 75 =
      ((55683789718674219808269469519884074 * 10 ^ 70 +
        8155095611012771295292110777456662744328633941339939204505041449521115) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_76 :
    remainder5Coefficient1.coeff 76 =
      -((71773194589557849430582637285555590 * 10 ^ 70 +
        0464336861567756238624503874974234256039546158770114337946374500744016) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_77 :
    remainder5Coefficient1.coeff 77 =
      ((88459000415688255401536702013611969 * 10 ^ 70 +
        2055935274931512972043592762038760647193996013469868075004960325258254) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_78 :
    remainder5Coefficient1.coeff 78 =
      -((104181909449697134798825256617201205 * 10 ^ 70 +
        2046982980144205215251939705895737777838282496905739211284947426952092) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_79 :
    remainder5Coefficient1.coeff 79 =
      ((117152932286896160528705451782234577 * 10 ^ 70 +
        3727316604543730825773918474294094830047892377492460614076233102857312) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_80 :
    remainder5Coefficient1.coeff 80 =
      -((125646967891916076365455898103245637 * 10 ^ 70 +
        3148787759601894169257866424209917877602285577248005226024999315143782) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_81 :
    remainder5Coefficient1.coeff 81 =
      ((128339748807534899191758880623368029 * 10 ^ 70 +
        1918839967780649202750197799380652208993110768963547060051632330317693) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_82 :
    remainder5Coefficient1.coeff 82 =
      -((124603962005887468537940198277894970 * 10 ^ 70 +
        0901918805242665368372861146248992055337322634897121428896457212950608) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_83 :
    remainder5Coefficient1.coeff 83 =
      ((114679802770548765775131674553523012 * 10 ^ 70 +
        1691193807801869751323090289444338208487672193991713137673883181927419) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_84 :
    remainder5Coefficient1.coeff 84 =
      -((99663920944982480597854668225328918 * 10 ^ 70 +
        3251337419108034336012450281045586616627122103451732432835090818807429) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_85 :
    remainder5Coefficient1.coeff 85 =
      ((81311150157989053420972502069536814 * 10 ^ 70 +
        3231864727386637690052997031326248837970792695250957580282997289735816) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_86 :
    remainder5Coefficient1.coeff 86 =
      -((61698337866845503226247017123087820 * 10 ^ 70 +
        3054080186671080782657207316726242154890583627835404800911447109140355) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
