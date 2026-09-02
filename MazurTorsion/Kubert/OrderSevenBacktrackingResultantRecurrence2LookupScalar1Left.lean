/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar1LeftPart0
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar1LeftPart1

/-!
# Recurrence 2 lookup certificate: Scalar1Left degree bound

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence2Scalar1Left_natDegree_le :
    recurrence2Scalar1Left.natDegree ≤ 382 := by
  unfold recurrence2Scalar1Left
  calc
    (recurrence2LeadingSquare * remainder2Coefficient1).natDegree ≤
        recurrence2LeadingSquare.natDegree + remainder2Coefficient1.natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 268 + 114 :=
      Nat.add_le_add recurrence2LeadingSquare_natDegree_le
        recurrence2A1_natDegree_le

theorem recurrence2Scalar1Left_coeff_high (n : ℕ) (h : 382 < n) :
    recurrence2Scalar1Left.coeff n = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  exact lt_of_le_of_lt recurrence2Scalar1Left_natDegree_le h

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
