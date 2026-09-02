/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar1ExceptionalPart0
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar1ExceptionalPart1
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar1ExceptionalPart2
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar1ExceptionalPart3
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar1ExceptionalPart4
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar1Exceptional degree bound

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4Scalar1Exceptional_coeff_0

theorem recurrence4Scalar1Exceptional_coeff_low (n : ℕ) (h : n < 1) :
    recurrence4Scalar1Exceptional.coeff n = 0 := by
  have hn : n = 0 := by omega
  subst n
  norm_num

theorem recurrence4Scalar1Exceptional_natDegree_le :
    recurrence4Scalar1Exceptional.natDegree ≤ 518 := by
  unfold recurrence4Scalar1Exceptional
  calc
    (recurrence4ExceptionalProduct * remainder6Coefficient1).natDegree ≤
        recurrence4ExceptionalProduct.natDegree + remainder6Coefficient1.natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 369 + 149 :=
      Nat.add_le_add recurrence4ExceptionalProduct_natDegree_le
        recurrence4C1_natDegree_le

theorem recurrence4Scalar1Exceptional_coeff_high (n : ℕ) (h : 518 < n) :
    recurrence4Scalar1Exceptional.coeff n = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  exact lt_of_le_of_lt recurrence4Scalar1Exceptional_natDegree_le h

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
