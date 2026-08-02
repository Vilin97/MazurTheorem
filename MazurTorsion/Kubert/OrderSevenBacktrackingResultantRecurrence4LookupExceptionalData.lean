/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData4
import Mathlib.Tactic.Ring

/-!
# Recurrence 4 lookup certificate: exceptional polynomial data

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

def recurrence4ExceptionalNormalizedBlock0 : Coefficient :=
  coefficientTerm 0 (
    (-1 : ℚ)) +
  coefficientTerm 1 (
    (-19 : ℚ)) +
  coefficientTerm 2 (
    (-98 : ℚ)) +
  coefficientTerm 3 (
    (94 : ℚ)) +
  coefficientTerm 4 (
    (1355 : ℚ)) +
  coefficientTerm 5 (
    (-1375 : ℚ)) +
  coefficientTerm 6 (
    (-7054 : ℚ)) +
  coefficientTerm 7 (
    (18910 : ℚ)) +
  coefficientTerm 8 (
    (-19802 : ℚ))

def recurrence4ExceptionalNormalizedBlock1 : Coefficient :=
  coefficientTerm 9 (
    (10514 : ℚ)) +
  coefficientTerm 10 (
    (-2928 : ℚ)) +
  coefficientTerm 11 (
    (436 : ℚ)) +
  coefficientTerm 12 (
    (-33 : ℚ)) +
  coefficientTerm 13 (
    (1 : ℚ))

def recurrence4ExceptionalNormalized : Coefficient :=
  recurrence4ExceptionalNormalizedBlock0 +
  recurrence4ExceptionalNormalizedBlock1

theorem exceptional4_eq_recurrence4ExceptionalNormalized :
    exceptional4 =
      exceptionalUnit4 * recurrence4ExceptionalNormalized := by
  unfold exceptional4 recurrence4ExceptionalNormalized
  unfold
    recurrence4ExceptionalNormalizedBlock0
    recurrence4ExceptionalNormalizedBlock1
  unfold discriminantFactor parameter
  simp only [coefficientTerm_eq_C_mul_X_pow]
  simp only [map_neg, map_ofNat, map_one]
  ring

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
