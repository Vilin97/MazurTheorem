/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar2ExceptionalPart0
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar2ExceptionalPart1
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar2ExceptionalPart2

/-!
# Recurrence 2 lookup certificate: Scalar2Exceptional degree bound

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence2Scalar2Exceptional_natDegree_le :
    recurrence2Scalar2Exceptional.natDegree ≤ 379 := by
  unfold recurrence2Scalar2Exceptional
  calc
    (recurrence2ExceptionalProduct * remainder4Coefficient2).natDegree ≤
        recurrence2ExceptionalProduct.natDegree + remainder4Coefficient2.natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 193 + 186 :=
      Nat.add_le_add recurrence2ExceptionalProduct_natDegree_le
        recurrence2C2_natDegree_le

theorem recurrence2Scalar2Exceptional_coeff_high (n : ℕ) (h : 379 < n) :
    recurrence2Scalar2Exceptional.coeff n = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  exact lt_of_le_of_lt recurrence2Scalar2Exceptional_natDegree_le h

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
