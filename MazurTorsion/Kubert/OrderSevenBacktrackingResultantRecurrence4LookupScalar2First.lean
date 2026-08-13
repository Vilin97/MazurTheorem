/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar2FirstPart0
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar2FirstPart1
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar2FirstPart2
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar2FirstPart3
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar2First degree bound

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4Scalar2First_coeff_0

theorem recurrence4Scalar2First_coeff_low (n : ℕ) (h : n < 1) :
    recurrence4Scalar2First.coeff n = 0 := by
  have hn : n = 0 := by omega
  subst n
  norm_num

theorem recurrence4Scalar2First_natDegree_le :
    recurrence4Scalar2First.natDegree ≤ 514 := by
  unfold recurrence4Scalar2First
  calc
    (remainder5Coefficient1 * recurrence4B3A4).natDegree ≤
        remainder5Coefficient1.natDegree + recurrence4B3A4.natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 172 + 342 :=
      Nat.add_le_add recurrence4B1_natDegree_le
        recurrence4B3A4_natDegree_le

theorem recurrence4Scalar2First_coeff_high (n : ℕ) (h : 514 < n) :
    recurrence4Scalar2First.coeff n = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  exact lt_of_le_of_lt recurrence4Scalar2First_natDegree_le h

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
