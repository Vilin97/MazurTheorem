/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar2SecondPart0
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar2SecondPart1
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar2SecondPart2
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar2SecondPart3

/-!
# Recurrence 4 lookup certificate: Scalar2Second degree bound

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence4Scalar2Second_natDegree_le :
    recurrence4Scalar2Second.natDegree ≤ 514 := by
  unfold recurrence4Scalar2Second
  calc
    (remainder5Coefficient2 * recurrence4QuotientConstant).natDegree ≤
        remainder5Coefficient2.natDegree + recurrence4QuotientConstant.natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 168 + 346 :=
      Nat.add_le_add recurrence4B2_natDegree_le
        recurrence4QuotientConstant_natDegree_le

theorem recurrence4Scalar2Second_coeff_high (n : ℕ) (h : 514 < n) :
    recurrence4Scalar2Second.coeff n = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  exact lt_of_le_of_lt recurrence4Scalar2Second_natDegree_le h

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
