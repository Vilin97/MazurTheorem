/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupScalar0LeftPart0
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupScalar0LeftPart1
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupScalar0LeftPart2

/-!
# Recurrence 5 lookup certificate: Scalar0Left degree bound

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence5Scalar0Left_natDegree_le :
    recurrence5Scalar0Left.natDegree ≤ 466 := by
  unfold recurrence5Scalar0Left
  calc
    (recurrence5LeadingSquare * remainder5Coefficient0).natDegree ≤
        recurrence5LeadingSquare.natDegree + remainder5Coefficient0.natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 290 + 176 :=
      Nat.add_le_add recurrence5LeadingSquare_natDegree_le
        recurrence5A0_natDegree_le

theorem recurrence5Scalar0Left_coeff_high (n : ℕ) (h : 466 < n) :
    recurrence5Scalar0Left.coeff n = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  exact lt_of_le_of_lt recurrence5Scalar0Left_natDegree_le h

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
