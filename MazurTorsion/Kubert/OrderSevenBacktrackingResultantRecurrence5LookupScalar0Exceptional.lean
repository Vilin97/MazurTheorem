/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupScalar0ExceptionalPart0
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupScalar0ExceptionalPart1
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupScalar0ExceptionalPart2

/-!
# Recurrence 5 lookup certificate: Scalar0Exceptional degree bound

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence5Scalar0Exceptional_natDegree_le :
    recurrence5Scalar0Exceptional.natDegree ≤ 466 := by
  unfold recurrence5Scalar0Exceptional
  calc
    (recurrence5ExceptionalProduct * remainder7Coefficient0).natDegree ≤
        recurrence5ExceptionalProduct.natDegree + remainder7Coefficient0.natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 378 + 88 :=
      Nat.add_le_add recurrence5ExceptionalProduct_natDegree_le
        recurrence5C0_natDegree_le

theorem recurrence5Scalar0Exceptional_coeff_high (n : ℕ) (h : 466 < n) :
    recurrence5Scalar0Exceptional.coeff n = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  exact lt_of_le_of_lt recurrence5Scalar0Exceptional_natDegree_le h

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
