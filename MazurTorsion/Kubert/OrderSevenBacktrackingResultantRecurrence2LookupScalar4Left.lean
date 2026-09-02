/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar4LeftPart0
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar4LeftPart1

/-!
# Recurrence 2 lookup certificate: Scalar4Left degree bound

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence2Scalar4Left_natDegree_le :
    recurrence2Scalar4Left.natDegree ≤ 370 := by
  unfold recurrence2Scalar4Left
  calc
    (recurrence2LeadingSquare * remainder2Coefficient4).natDegree ≤
        recurrence2LeadingSquare.natDegree + remainder2Coefficient4.natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 268 + 102 :=
      Nat.add_le_add recurrence2LeadingSquare_natDegree_le
        recurrence2A4_natDegree_le

theorem recurrence2Scalar4Left_coeff_high (n : ℕ) (h : 370 < n) :
    recurrence2Scalar4Left.coeff n = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  exact lt_of_le_of_lt recurrence2Scalar4Left_natDegree_le h

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
