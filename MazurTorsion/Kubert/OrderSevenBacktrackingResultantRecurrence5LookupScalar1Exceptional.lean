/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupScalar1ExceptionalPart0
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupScalar1ExceptionalPart1
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupScalar1ExceptionalPart2

/-!
# Recurrence 5 lookup certificate: Scalar1Exceptional degree bound

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence5Scalar1Exceptional_natDegree_le :
    recurrence5Scalar1Exceptional.natDegree ≤ 462 := by
  unfold recurrence5Scalar1Exceptional
  calc
    (recurrence5ExceptionalProduct * remainder7Coefficient1).natDegree ≤
        recurrence5ExceptionalProduct.natDegree + remainder7Coefficient1.natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 378 + 84 :=
      Nat.add_le_add recurrence5ExceptionalProduct_natDegree_le
        recurrence5C1_natDegree_le

theorem recurrence5Scalar1Exceptional_coeff_high (n : ℕ) (h : 462 < n) :
    recurrence5Scalar1Exceptional.coeff n = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  exact lt_of_le_of_lt recurrence5Scalar1Exceptional_natDegree_le h

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
