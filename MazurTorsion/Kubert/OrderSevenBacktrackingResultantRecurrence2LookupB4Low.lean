/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData2
import Mathlib.Tactic.NormNum

/-!
# Recurrence 2 lookup certificate: B4 source coefficients, low half

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence2B4_coeff_0 :
    remainder3Coefficient4.coeff 0 =
      (0 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_1 :
    remainder3Coefficient4.coeff 1 =
      (-488 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_2 :
    remainder3Coefficient4.coeff 2 =
      (79908936 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_3 :
    remainder3Coefficient4.coeff 3 =
      (-54171772584 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_4 :
    remainder3Coefficient4.coeff 4 =
      (74645004683336 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_5 :
    remainder3Coefficient4.coeff 5 =
      (-29051618894656499 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_6 :
    remainder3Coefficient4.coeff 6 =
      (7886790788452359315 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_7 :
    remainder3Coefficient4.coeff 7 =
      (-1278370368188845513764 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_8 :
    remainder3Coefficient4.coeff 8 =
      (140987840827161338457851 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_9 :
    remainder3Coefficient4.coeff 9 =
      (-10701779933849849433844089 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_10 :
    remainder3Coefficient4.coeff 10 =
      (588152189587661323715172081 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_11 :
    remainder3Coefficient4.coeff 11 =
      (-24167814127891687580020207335 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_12 :
    remainder3Coefficient4.coeff 12 =
      (729195980181088218206280942700 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_13 :
    remainder3Coefficient4.coeff 13 =
      (-8895471790438980058846996164913 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_14 :
    remainder3Coefficient4.coeff 14 =
      (-882612127378855411361653196714648 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_15 :
    remainder3Coefficient4.coeff 15 =
      (89365878071942030982913958852886304 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_16 :
    remainder3Coefficient4.coeff 16 =
      (-4923582587274649083139695798829936769 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_17 :
    remainder3Coefficient4.coeff 17 =
      (193360427385813188975621594468990858686 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_18 :
    remainder3Coefficient4.coeff 18 =
      (-5788532679887554975261205198967747686851 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_19 :
    remainder3Coefficient4.coeff 19 =
      (135288248224309717839398853453681221533696 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_20 :
    remainder3Coefficient4.coeff 20 =
      (-2462609013470166402268531714867748618199639 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_21 :
    remainder3Coefficient4.coeff 21 =
      (33339758442488426345554443264033565017930115 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_22 :
    remainder3Coefficient4.coeff 22 =
      (-270679302557652162589462507020207511690718005 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_23 :
    remainder3Coefficient4.coeff 23 =
      (-1008818495035685879478047562937998290862155503 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_24 :
    remainder3Coefficient4.coeff 24 =
      (87859518738094204518914861028615064599069473206 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_25 :
    remainder3Coefficient4.coeff 25 =
      (-1996446506939477995085583788522015464054736054877 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_26 :
    remainder3Coefficient4.coeff 26 =
      (32007005156281181505856727509883767105293103004514 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_27 :
    remainder3Coefficient4.coeff 27 =
      (-414475844456614144844151244654497319796243288778674 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_28 :
    remainder3Coefficient4.coeff 28 =
      (4553400933006248078802631154823702817095792105900271 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_29 :
    remainder3Coefficient4.coeff 29 =
      (-43490965361797663125814311585276534845596882357840770 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_30 :
    remainder3Coefficient4.coeff 30 =
      (366411820327147359441537506283766953887904168172066702 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_31 :
    remainder3Coefficient4.coeff 31 =
      (-2748502211711448991639651408908403456731970402167966495 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_32 :
    remainder3Coefficient4.coeff 32 =
      (18470328906533137619902866800115673246183364037582400911 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_33 :
    remainder3Coefficient4.coeff 33 =
      (-111648682526514395867932171694428172751902103118003413560 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_34 :
    remainder3Coefficient4.coeff 34 =
      (608432329238316096883754444681345561559019896743515021197 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_35 :
    remainder3Coefficient4.coeff 35 =
      (-2990695177461363061406833255061234766763411781951336165514 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_36 :
    remainder3Coefficient4.coeff 36 =
      (13237718815493998019899288784617610290798803012441576727343 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_37 :
    remainder3Coefficient4.coeff 37 =
      (-52502605798787872119996775014233460522634368465938442985043 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_38 :
    remainder3Coefficient4.coeff 38 =
      (184579337456064638954568715230795236941493505519635632580955 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_39 :
    remainder3Coefficient4.coeff 39 =
      (-562236680128760107962573419031430712207619710315337358381305 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_40 :
    remainder3Coefficient4.coeff 40 =
      (1406307149455739623594356861532069650456895070659381148711193 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_41 :
    remainder3Coefficient4.coeff 41 =
      (-2423850189762669748208799419426172192321523993140498066104006 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_42 :
    remainder3Coefficient4.coeff 42 =
      (-197336827839669322632473451657661860781238967613539597953615 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_43 :
    remainder3Coefficient4.coeff 43 =
      (24854031952164914996894325056269314301931991893396923723541266 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_44 :
    remainder3Coefficient4.coeff 44 =
      (-138215545453863210538475321355045517286365246515311416313462181 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_45 :
    remainder3Coefficient4.coeff 45 =
      (542576334946524184941790668853533285102927230254261096629654661 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_46 :
    remainder3Coefficient4.coeff 46 =
      (-1755657688136356897476181133016516604599131969331912417823621915 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_47 :
    remainder3Coefficient4.coeff 47 =
      (4824953892101361868840861253802219905285789358070456586664162781 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_48 :
    remainder3Coefficient4.coeff 48 =
      (-11188907154916730751431668524239029812334343868615229025696267272 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_49 :
    remainder3Coefficient4.coeff 49 =
      (22159876195200541825288614976241194304914096854983463400518814819 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_50 :
    remainder3Coefficient4.coeff 50 =
      (-43878357774793283803705695084308372379342153863154742382676829337 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_51 :
    remainder3Coefficient4.coeff 51 =
      (116168706880217995187833923198595633714237637222029887934310148860 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_52 :
    remainder3Coefficient4.coeff 52 =
      (-331531685124414616494006930352859635083193832697486716593344284348 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_53 :
    remainder3Coefficient4.coeff 53 =
      (416781706939311167391295573343303108140942582076923175022422653348 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_54 :
    remainder3Coefficient4.coeff 54 =
      (2288057942395516301874537037127348688860236592066239956523068698194 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_55 :
    remainder3Coefficient4.coeff 55 =
      (-15027005393041491111291775726982408973660731111581889612795188198276 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_56 :
    remainder3Coefficient4.coeff 56 =
      (31205787281616005358739491370661912562932163198191396863724752762504 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_57 :
    remainder3Coefficient4.coeff 57 =
      (70824160951855985857684626573077506889865415795629591025559933421298 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_58 :
    remainder3Coefficient4.coeff 58 =
      (-704329761420437485860504450663813125601364110836143296241149336499616 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_59 :
    remainder3Coefficient4.coeff 59 =
      (2096673518452005734254197699408252886561028548057257693744437477509923 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_60 :
    remainder3Coefficient4.coeff 60 =
      (-429095125300578788538477178154569570773685060326131013651589371659683 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_61 :
    remainder3Coefficient4.coeff 61 =
      -((2 * 10 ^ 70 +
        2492281016135882505333965254250250313578373468918714135682932527214861) : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_62 :
    remainder3Coefficient4.coeff 62 =
      ((10 * 10 ^ 70 +
        1558558039385865222836294369420977249002541350024726686687301932041169) : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_63 :
    remainder3Coefficient4.coeff 63 =
      -((19 * 10 ^ 70 +
        8652577094721135931073178264219316140899172164130278500653729568501592) : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_64 :
    remainder3Coefficient4.coeff 64 =
      -((17 * 10 ^ 70 +
        6565239946859853473116379656727546168794978080509620418351549224155658) : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_65 :
    remainder3Coefficient4.coeff 65 =
      ((270 * 10 ^ 70 +
        2953007588566631629174960270157122332606142430035329079709240392592458) : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_66 :
    remainder3Coefficient4.coeff 66 =
      -((1006 * 10 ^ 70 +
        3842118408960246637724608263283382533914182735720419176302758058387438) : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_67 :
    remainder3Coefficient4.coeff 67 =
      ((1945 * 10 ^ 70 +
        6360616319541174764935443622590468639352927797789194888322544251300231) : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_68 :
    remainder3Coefficient4.coeff 68 =
      ((192 * 10 ^ 70 +
        2214155732299846269579554624683053779207647506245495350597584069315180) : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_69 :
    remainder3Coefficient4.coeff 69 =
      -((16893 * 10 ^ 70 +
        9163095657195668981069001406276089211626802206649683371629930986218430) : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
