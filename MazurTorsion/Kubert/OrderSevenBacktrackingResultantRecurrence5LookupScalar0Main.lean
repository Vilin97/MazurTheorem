/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupScalar0MainPart0
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupScalar0MainPart1
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupScalar0MainPart2

/-!
# Recurrence 5 lookup certificate: Scalar0Main degree bound

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence5Scalar0Main_natDegree_le :
    recurrence5Scalar0Main.natDegree ≤ 466 := by
  unfold recurrence5Scalar0Main
  calc
    (remainder6Coefficient0 * recurrence5QuotientConstant).natDegree ≤
        remainder6Coefficient0.natDegree + recurrence5QuotientConstant.natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 153 + 313 :=
      Nat.add_le_add recurrence5B0_natDegree_le
        recurrence5QuotientConstant_natDegree_le

theorem recurrence5Scalar0Main_coeff_high (n : ℕ) (h : 466 < n) :
    recurrence5Scalar0Main.coeff n = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  exact lt_of_le_of_lt recurrence5Scalar0Main_natDegree_le h

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
