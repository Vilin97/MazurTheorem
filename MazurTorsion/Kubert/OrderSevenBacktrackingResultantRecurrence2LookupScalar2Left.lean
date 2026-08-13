/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar2LeftPart0
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar2LeftPart1

/-!
# Recurrence 2 lookup certificate: Scalar2Left degree bound

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence2Scalar2Left_natDegree_le :
    recurrence2Scalar2Left.natDegree ≤ 378 := by
  unfold recurrence2Scalar2Left
  calc
    (recurrence2LeadingSquare * remainder2Coefficient2).natDegree ≤
        recurrence2LeadingSquare.natDegree + remainder2Coefficient2.natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 268 + 110 :=
      Nat.add_le_add recurrence2LeadingSquare_natDegree_le
        recurrence2A2_natDegree_le

theorem recurrence2Scalar2Left_coeff_high (n : ℕ) (h : 378 < n) :
    recurrence2Scalar2Left.coeff n = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  exact lt_of_le_of_lt recurrence2Scalar2Left_natDegree_le h

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
