/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1Bridge
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1QuotientConstant
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1NormalizedInner0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1NormalizedInner1
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1NormalizedInner2
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1NormalizedInner3
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1NormalizedInner4
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1NormalizedInner5

import Mathlib.Tactic.Ring

/-!
# Recurrence 1 certificate: Inner

This file is a checked bounded-band arithmetic shard for the first
pseudo-division recurrence in the order-seven branch-zero resultant certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence1_inner_0 :
    remainder2Coefficient6 ^ 2 *
      Internal.divisionCofactor0Coefficient0 =
        remainder2Coefficient0 *
          (remainder2Coefficient6 *
              Internal.divisionCofactor0Coefficient6 -
            remainder2Coefficient5 *
              Internal.divisionCofactor0Coefficient7) +
        (Internal.divisionCofactor0Coefficient7 ^ 2 *
            exceptional1) *
          remainder3Coefficient0 := by
  rw [divisionCofactor0Coefficient0_eq_normalized]
  rw [divisionCofactor0Coefficient6_eq_normalized]
  rw [divisionCofactor0Coefficient7_eq_normalized]
  rw [remainder2Coefficient0_eq_normalized]
  rw [remainder2Coefficient5_eq_normalized]
  rw [remainder2Coefficient6_eq_normalized]
  rw [remainder3Coefficient0_eq_normalized]
  rw [exceptional1_eq_normalized]
  rw [recurrence1QuotientConstant_eq]
  simpa [recurrence1Source7, recurrence1Source7Block0]
    using recurrence1NormalizedInner0

theorem recurrence1_inner_1 :
    remainder2Coefficient6 ^ 2 *
      Internal.divisionCofactor0Coefficient1 =
      remainder2Coefficient0 *
          (remainder2Coefficient6 *
            Internal.divisionCofactor0Coefficient7) +
        remainder2Coefficient1 *
          (remainder2Coefficient6 *
              Internal.divisionCofactor0Coefficient6 -
            remainder2Coefficient5 *
              Internal.divisionCofactor0Coefficient7) +
        (Internal.divisionCofactor0Coefficient7 ^ 2 *
            exceptional1) *
          remainder3Coefficient1 := by
  rw [divisionCofactor0Coefficient1_eq_normalized]
  rw [divisionCofactor0Coefficient6_eq_normalized]
  rw [divisionCofactor0Coefficient7_eq_normalized]
  rw [remainder2Coefficient1_eq_normalized]
  rw [remainder2Coefficient5_eq_normalized]
  rw [remainder2Coefficient6_eq_normalized]
  rw [remainder3Coefficient1_eq_normalized]
  rw [exceptional1_eq_normalized]
  rw [remainder2Coefficient0_eq_normalized]
  rw [recurrence1QuotientConstant_eq]
  simpa [recurrence1Source7, recurrence1Source7Block0]
    using recurrence1NormalizedInner1

theorem recurrence1_inner_2 :
    remainder2Coefficient6 ^ 2 *
      Internal.divisionCofactor0Coefficient2 =
      remainder2Coefficient1 *
          (remainder2Coefficient6 *
            Internal.divisionCofactor0Coefficient7) +
        remainder2Coefficient2 *
          (remainder2Coefficient6 *
              Internal.divisionCofactor0Coefficient6 -
            remainder2Coefficient5 *
              Internal.divisionCofactor0Coefficient7) +
        (Internal.divisionCofactor0Coefficient7 ^ 2 *
            exceptional1) *
          remainder3Coefficient2 := by
  rw [divisionCofactor0Coefficient2_eq_normalized]
  rw [divisionCofactor0Coefficient6_eq_normalized]
  rw [divisionCofactor0Coefficient7_eq_normalized]
  rw [remainder2Coefficient2_eq_normalized]
  rw [remainder2Coefficient5_eq_normalized]
  rw [remainder2Coefficient6_eq_normalized]
  rw [remainder3Coefficient2_eq_normalized]
  rw [exceptional1_eq_normalized]
  rw [remainder2Coefficient1_eq_normalized]
  rw [recurrence1QuotientConstant_eq]
  simpa [recurrence1Source7, recurrence1Source7Block0]
    using recurrence1NormalizedInner2

theorem recurrence1_inner_3 :
    remainder2Coefficient6 ^ 2 *
      Internal.divisionCofactor0Coefficient3 =
      remainder2Coefficient2 *
          (remainder2Coefficient6 *
            Internal.divisionCofactor0Coefficient7) +
        remainder2Coefficient3 *
          (remainder2Coefficient6 *
              Internal.divisionCofactor0Coefficient6 -
            remainder2Coefficient5 *
              Internal.divisionCofactor0Coefficient7) +
        (Internal.divisionCofactor0Coefficient7 ^ 2 *
            exceptional1) *
          remainder3Coefficient3 := by
  rw [divisionCofactor0Coefficient3_eq_normalized]
  rw [divisionCofactor0Coefficient6_eq_normalized]
  rw [divisionCofactor0Coefficient7_eq_normalized]
  rw [remainder2Coefficient3_eq_normalized]
  rw [remainder2Coefficient5_eq_normalized]
  rw [remainder2Coefficient6_eq_normalized]
  rw [remainder3Coefficient3_eq_normalized]
  rw [exceptional1_eq_normalized]
  rw [remainder2Coefficient2_eq_normalized]
  rw [recurrence1QuotientConstant_eq]
  simpa [recurrence1Source7, recurrence1Source7Block0]
    using recurrence1NormalizedInner3

theorem recurrence1_inner_4 :
    remainder2Coefficient6 ^ 2 *
      Internal.divisionCofactor0Coefficient4 =
      remainder2Coefficient3 *
          (remainder2Coefficient6 *
            Internal.divisionCofactor0Coefficient7) +
        remainder2Coefficient4 *
          (remainder2Coefficient6 *
              Internal.divisionCofactor0Coefficient6 -
            remainder2Coefficient5 *
              Internal.divisionCofactor0Coefficient7) +
        (Internal.divisionCofactor0Coefficient7 ^ 2 *
            exceptional1) *
          remainder3Coefficient4 := by
  rw [divisionCofactor0Coefficient4_eq_normalized]
  rw [divisionCofactor0Coefficient6_eq_normalized]
  rw [divisionCofactor0Coefficient7_eq_normalized]
  rw [remainder2Coefficient4_eq_normalized]
  rw [remainder2Coefficient5_eq_normalized]
  rw [remainder2Coefficient6_eq_normalized]
  rw [remainder3Coefficient4_eq_normalized]
  rw [exceptional1_eq_normalized]
  rw [remainder2Coefficient3_eq_normalized]
  rw [recurrence1QuotientConstant_eq]
  simpa [recurrence1Source7, recurrence1Source7Block0]
    using recurrence1NormalizedInner4

theorem recurrence1_inner_5 :
    remainder2Coefficient6 ^ 2 *
      Internal.divisionCofactor0Coefficient5 =
      remainder2Coefficient4 *
          (remainder2Coefficient6 *
            Internal.divisionCofactor0Coefficient7) +
        remainder2Coefficient5 *
          (remainder2Coefficient6 *
              Internal.divisionCofactor0Coefficient6 -
            remainder2Coefficient5 *
              Internal.divisionCofactor0Coefficient7) +
        (Internal.divisionCofactor0Coefficient7 ^ 2 *
            exceptional1) *
          remainder3Coefficient5 := by
  rw [divisionCofactor0Coefficient5_eq_normalized]
  rw [divisionCofactor0Coefficient6_eq_normalized]
  rw [divisionCofactor0Coefficient7_eq_normalized]
  rw [remainder2Coefficient5_eq_normalized]
  rw [remainder2Coefficient6_eq_normalized]
  rw [remainder3Coefficient5_eq_normalized]
  rw [exceptional1_eq_normalized]
  rw [remainder2Coefficient4_eq_normalized]
  rw [recurrence1QuotientConstant_eq]
  simpa [recurrence1Source7, recurrence1Source7Block0]
    using recurrence1NormalizedInner5

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
