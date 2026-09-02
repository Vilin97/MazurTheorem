/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar1MainPart0
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar1MainPart1
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar1MainPart2

/-!
# Recurrence 2 lookup certificate: Scalar1Main degree bound

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence2Scalar1Main_natDegree_le :
    recurrence2Scalar1Main.natDegree ≤ 383 := by
  unfold recurrence2Scalar1Main
  calc
    (remainder3Coefficient1 * recurrence2QuotientConstant).natDegree ≤
        remainder3Coefficient1.natDegree + recurrence2QuotientConstant.natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 150 + 233 :=
      Nat.add_le_add recurrence2B1_natDegree_le
        recurrence2QuotientConstant_natDegree_le

theorem recurrence2Scalar1Main_coeff_high (n : ℕ) (h : 383 < n) :
    recurrence2Scalar1Main.coeff n = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  exact lt_of_le_of_lt recurrence2Scalar1Main_natDegree_le h

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
