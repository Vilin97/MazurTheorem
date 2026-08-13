/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupExceptionalProductPart0

/-!
# Recurrence 2 lookup certificate: ExceptionalProduct degree bound

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence2ExceptionalProduct_natDegree_le :
    recurrence2ExceptionalProduct.natDegree ≤ 193 := by
  unfold recurrence2ExceptionalProduct
  calc
    (recurrence2A6Square * exceptional2).natDegree ≤
        recurrence2A6Square.natDegree + exceptional2.natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 190 + 3 :=
      Nat.add_le_add recurrence2A6Square_natDegree_le
        recurrence2Exceptional_natDegree_le

theorem recurrence2ExceptionalProduct_coeff_high (n : ℕ) (h : 193 < n) :
    recurrence2ExceptionalProduct.coeff n = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  exact lt_of_le_of_lt recurrence2ExceptionalProduct_natDegree_le h

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
