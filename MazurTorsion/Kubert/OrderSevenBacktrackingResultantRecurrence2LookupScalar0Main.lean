/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar0MainPart0
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar0MainPart1
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar0MainPart2

/-!
# Recurrence 2 lookup certificate: Scalar0Main degree bound

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence2Scalar0Main_natDegree_le :
    recurrence2Scalar0Main.natDegree ≤ 387 := by
  unfold recurrence2Scalar0Main
  calc
    (remainder3Coefficient0 * recurrence2QuotientConstant).natDegree ≤
        remainder3Coefficient0.natDegree + recurrence2QuotientConstant.natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 154 + 233 :=
      Nat.add_le_add recurrence2B0_natDegree_le
        recurrence2QuotientConstant_natDegree_le

theorem recurrence2Scalar0Main_coeff_high (n : ℕ) (h : 387 < n) :
    recurrence2Scalar0Main.coeff n = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  exact lt_of_le_of_lt recurrence2Scalar0Main_natDegree_le h

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
