/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar2ExceptionalPart0
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar2ExceptionalPart1
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar2ExceptionalPart2
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar2ExceptionalPart3

/-!
# Recurrence 4 lookup certificate: Scalar2Exceptional degree bound

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence4Scalar2Exceptional_natDegree_le :
    recurrence4Scalar2Exceptional.natDegree ≤ 514 := by
  unfold recurrence4Scalar2Exceptional
  calc
    (recurrence4ExceptionalProduct * remainder6Coefficient2).natDegree ≤
        recurrence4ExceptionalProduct.natDegree + remainder6Coefficient2.natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 369 + 145 :=
      Nat.add_le_add recurrence4ExceptionalProduct_natDegree_le
        recurrence4C2_natDegree_le

theorem recurrence4Scalar2Exceptional_coeff_high (n : ℕ) (h : 514 < n) :
    recurrence4Scalar2Exceptional.coeff n = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  exact lt_of_le_of_lt recurrence4Scalar2Exceptional_natDegree_le h

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
