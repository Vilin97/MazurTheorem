/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData2
import Mathlib.Tactic.NormNum

/-!
# Recurrence 2 lookup certificate: B1 source coefficients, low half

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence2B1_coeff_0 :
    remainder3Coefficient1.coeff 0 =
      (0 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_1 :
    remainder3Coefficient1.coeff 1 =
      (0 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_2 :
    remainder3Coefficient1.coeff 2 =
      (790 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_3 :
    remainder3Coefficient1.coeff 3 =
      (13593174 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_4 :
    remainder3Coefficient1.coeff 4 =
      (-3143765912 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_5 :
    remainder3Coefficient1.coeff 5 =
      (22224431529139 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_6 :
    remainder3Coefficient1.coeff 6 =
      (-9581546513540763 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_7 :
    remainder3Coefficient1.coeff 7 =
      (3625768004123046781 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_8 :
    remainder3Coefficient1.coeff 8 =
      (-736427900725824578076 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_9 :
    remainder3Coefficient1.coeff 9 =
      (103602730525610362262883 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_10 :
    remainder3Coefficient1.coeff 10 =
      (-9720000525951758301319245 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_11 :
    remainder3Coefficient1.coeff 11 =
      (641384061688276159506992347 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_12 :
    remainder3Coefficient1.coeff 12 =
      (-29807610346047288542981828167 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_13 :
    remainder3Coefficient1.coeff 13 =
      (1011993514928827874626255085507 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_14 :
    remainder3Coefficient1.coeff 14 =
      (-27588785382850700761419492527289 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_15 :
    remainder3Coefficient1.coeff 15 =
      (778856192928799753253598015152603 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_16 :
    remainder3Coefficient1.coeff 16 =
      (-26284968749545126326416226531774290 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_17 :
    remainder3Coefficient1.coeff 17 =
      (838677187750941599932471485344008670 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_18 :
    remainder3Coefficient1.coeff 18 =
      (-19840159097813206912112856692962029068 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_19 :
    remainder3Coefficient1.coeff 19 =
      (283995824988650272088359232893564919176 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_20 :
    remainder3Coefficient1.coeff 20 =
      (-200658286951553508779688024152928626651 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_21 :
    remainder3Coefficient1.coeff 21 =
      (-120919132753601655772668751345790687120650 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_22 :
    remainder3Coefficient1.coeff 22 =
      (4455966837412600171978384930666283132335687 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_23 :
    remainder3Coefficient1.coeff 23 =
      (-120077005830542256214571792357570834586972659 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_24 :
    remainder3Coefficient1.coeff 24 =
      (2902315697149986652200100169000154423713480755 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_25 :
    remainder3Coefficient1.coeff 25 =
      (-64526473845662151335844662172009059089429794440 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_26 :
    remainder3Coefficient1.coeff 26 =
      (1290617704867752262141072773114910620724348839175 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_27 :
    remainder3Coefficient1.coeff 27 =
      (-22794729084532014995478647727817834396948459520021 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_28 :
    remainder3Coefficient1.coeff 28 =
      (353315556448081185199307400698484199360270721194167 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_29 :
    remainder3Coefficient1.coeff 29 =
      (-4812880786691912788110047237084103655447978586593530 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_30 :
    remainder3Coefficient1.coeff 30 =
      (57878291146815460358092129376595562590210734151862692 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_31 :
    remainder3Coefficient1.coeff 31 =
      (-617737352359349426905107435023724165392922381504137923 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_32 :
    remainder3Coefficient1.coeff 32 =
      (5882473491592880845864414439966373119811884720514047408 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_33 :
    remainder3Coefficient1.coeff 33 =
      (-50225332563756226781419166424600265060827872658557808475 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_34 :
    remainder3Coefficient1.coeff 34 =
      (386197339368419763052534094787306808064088847892188612625 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_35 :
    remainder3Coefficient1.coeff 35 =
      (-2684385573847498095843446412228192123945573443457869640978 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_36 :
    remainder3Coefficient1.coeff 36 =
      (16915745887002034351475883518944567198214998221214373419499 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_37 :
    remainder3Coefficient1.coeff 37 =
      (-96824403862890422932058276712182234587757995442593103229009 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_38 :
    remainder3Coefficient1.coeff 38 =
      (503844983252797470837528502548084963562855064376136786810227 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_39 :
    remainder3Coefficient1.coeff 39 =
      (-2382798511493624516680177675176011018883559732018875565761936 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_40 :
    remainder3Coefficient1.coeff 40 =
      (10223013125965829245523948751685394125642246592829054736465168 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_41 :
    remainder3Coefficient1.coeff 41 =
      (-39627501507429808811790196833806911471089677385973947886850912 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_42 :
    remainder3Coefficient1.coeff 42 =
      (137616328417704194525298358145366065885753892096244508687775525 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_43 :
    remainder3Coefficient1.coeff 43 =
      (-420617832937282719549932530428156073690217654863162183515867533 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_44 :
    remainder3Coefficient1.coeff 44 =
      (1086688077016891640040404719916952250758001709002929849819100269 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_45 :
    remainder3Coefficient1.coeff 45 =
      (-2117045900378094450302394180197976052020697874866389261529290053 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_46 :
    remainder3Coefficient1.coeff 46 =
      (1573873370402300220999391826761829897204425586926558504077729681 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_47 :
    remainder3Coefficient1.coeff 47 =
      (10644311786833732656582735778162373125475408995102187543542544923 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_48 :
    remainder3Coefficient1.coeff 48 =
      (-71136715030969184183854200060725777190148445001450823149086923021 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_49 :
    remainder3Coefficient1.coeff 49 =
      (292069722490930185310853946295842046672642764572343504310414030087 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_50 :
    remainder3Coefficient1.coeff 50 =
      (-993393455921345980841725671678556174931105337591928892889947841542 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_51 :
    remainder3Coefficient1.coeff 51 =
      (3023085324759856524499293283672137920340087897186076737631493632750 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_52 :
    remainder3Coefficient1.coeff 52 =
      (-8104447679923438559902964456472011977417072409659123493088766295176 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_53 :
    remainder3Coefficient1.coeff 53 =
      (17068731288293475113119521168870069874789814003682746242005916945360 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_54 :
    remainder3Coefficient1.coeff 54 =
      (-19928043604410636555449239072426940875229149351481373517789242548598 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_55 :
    remainder3Coefficient1.coeff 55 =
      (-13406571249791003147339517709710462822381192608530851772516857429164 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_56 :
    remainder3Coefficient1.coeff 56 =
      (16337173046674659333592019656472193136943084993896137745116502038120 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_57 :
    remainder3Coefficient1.coeff 57 =
      (788244571679145887294001151407222542857474774728122808576916171988427 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_58 :
    remainder3Coefficient1.coeff 58 =
      (-4720544453607848933345905252674414508285957488103489946389986149675376 : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_59 :
    remainder3Coefficient1.coeff 59 =
      ((1 * 10 ^ 70 +
        0541615416793286959116889447018063695759759247843859465082481202079933) : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_60 :
    remainder3Coefficient1.coeff 60 =
      ((1 * 10 ^ 70 +
        9057956045469880482016929997469405733565450970846524356670318413745663) : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_61 :
    remainder3Coefficient1.coeff 61 =
      -((22 * 10 ^ 70 +
        9234680572595593158202990957944906398901149263780505360321775093890590) : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_62 :
    remainder3Coefficient1.coeff 62 =
      ((78 * 10 ^ 70 +
        0833008966444051047835542198098936282536197180909773443671782123198606) : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_63 :
    remainder3Coefficient1.coeff 63 =
      -((63 * 10 ^ 70 +
        4880177846232697069663772185982670415648143436134681720696102204307272) : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_64 :
    remainder3Coefficient1.coeff 64 =
      -((652 * 10 ^ 70 +
        7460295408561257167332988789855457353847879369243876202961901336308128) : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_65 :
    remainder3Coefficient1.coeff 65 =
      ((3660 * 10 ^ 70 +
        3393159720128532642111962270836208076149013765143528862926056211777128) : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_66 :
    remainder3Coefficient1.coeff 66 =
      -((9202 * 10 ^ 70 +
        9916592950937771569915357495182546134341107195158563384457280187594141) : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_67 :
    remainder3Coefficient1.coeff 67 =
      ((2391 * 10 ^ 70 +
        6344032483543070847613672697816675629296352215354705655717478907851007) : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_68 :
    remainder3Coefficient1.coeff 68 =
      ((83439 * 10 ^ 70 +
        7404747305773033159661648892678823750538762615391283413824994843324864) : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_69 :
    remainder3Coefficient1.coeff 69 =
      -((399630 * 10 ^ 70 +
        3655923177312452137471167100825147480661468764582415270062702396828521) : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_70 :
    remainder3Coefficient1.coeff 70 =
      ((1014452 * 10 ^ 70 +
        6130743151480975052942590838687807536124908615956530007344433566950721) : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_71 :
    remainder3Coefficient1.coeff 71 =
      -((951000 * 10 ^ 70 +
        9682626456726579735199708352255118508295802156374570801873286903511519) : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_72 :
    remainder3Coefficient1.coeff 72 =
      -((4562026 * 10 ^ 70 +
        3581110809638804385783434895481376722178741641478022374645621764749733) : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_73 :
    remainder3Coefficient1.coeff 73 =
      ((28645249 * 10 ^ 70 +
        2630542240220701359832941097694136397329407855152621898353506403112908) : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_74 :
    remainder3Coefficient1.coeff 74 =
      -((93011432 * 10 ^ 70 +
        3269042709597186787827597165949689489156861307830371574582153217620640) : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B1_coeff_75 :
    remainder3Coefficient1.coeff 75 =
      ((199686410 * 10 ^ 70 +
        6811636042452265558222841452121479111209476815590003680762080409656459) : ℚ) := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
    remainder3Coefficient1Chunk18
    remainder3Coefficient1Chunk17
    remainder3Coefficient1Chunk16
    remainder3Coefficient1Chunk15
    remainder3Coefficient1Chunk14
    remainder3Coefficient1Chunk13
    remainder3Coefficient1Chunk12
    remainder3Coefficient1Chunk11
    remainder3Coefficient1Chunk10
    remainder3Coefficient1Chunk9
    remainder3Coefficient1Chunk8
    remainder3Coefficient1Chunk7
    remainder3Coefficient1Chunk6
    remainder3Coefficient1Chunk5
    remainder3Coefficient1Chunk4
    remainder3Coefficient1Chunk3
    remainder3Coefficient1Chunk2
    remainder3Coefficient1Chunk1
    remainder3Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
