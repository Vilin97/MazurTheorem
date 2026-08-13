/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar2LeftPart0
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar2LeftPart1
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar2LeftPart2
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar2LeftPart3

/-!
# Recurrence 4 lookup certificate: Scalar2Left degree bound

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence4Scalar2Left_natDegree_le :
    recurrence4Scalar2Left.natDegree ≤ 514 := by
  unfold recurrence4Scalar2Left
  calc
    (recurrence4LeadingSquare * remainder4Coefficient2).natDegree ≤
        recurrence4LeadingSquare.natDegree + remainder4Coefficient2.natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 328 + 186 :=
      Nat.add_le_add recurrence4LeadingSquare_natDegree_le
        recurrence4A2_natDegree_le

theorem recurrence4Scalar2Left_coeff_high (n : ℕ) (h : 514 < n) :
    recurrence4Scalar2Left.coeff n = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  exact lt_of_le_of_lt recurrence4Scalar2Left_natDegree_le h

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
