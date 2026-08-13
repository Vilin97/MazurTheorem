/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar1SecondPart0
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar1SecondPart1
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar1SecondPart2
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar1SecondPart3
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar1SecondPart4
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar1Second degree bound

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4Scalar1Second_coeff_0

theorem recurrence4Scalar1Second_coeff_low (n : ℕ) (h : n < 1) :
    recurrence4Scalar1Second.coeff n = 0 := by
  have hn : n = 0 := by omega
  subst n
  norm_num

theorem recurrence4Scalar1Second_natDegree_le :
    recurrence4Scalar1Second.natDegree ≤ 518 := by
  unfold recurrence4Scalar1Second
  calc
    (remainder5Coefficient1 * recurrence4QuotientConstant).natDegree ≤
        remainder5Coefficient1.natDegree + recurrence4QuotientConstant.natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 172 + 346 :=
      Nat.add_le_add recurrence4B1_natDegree_le
        recurrence4QuotientConstant_natDegree_le

theorem recurrence4Scalar1Second_coeff_high (n : ℕ) (h : 518 < n) :
    recurrence4Scalar1Second.coeff n = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  exact lt_of_le_of_lt recurrence4Scalar1Second_natDegree_le h

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
