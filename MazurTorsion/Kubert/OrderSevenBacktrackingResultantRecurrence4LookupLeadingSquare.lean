/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupLeadingSquarePart0
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupLeadingSquarePart1

/-!
# Recurrence 4 lookup certificate: LeadingSquare degree bound

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence4LeadingSquare_natDegree_le :
    recurrence4LeadingSquare.natDegree ≤ 328 := by
  unfold recurrence4LeadingSquare
  calc
    (remainder5Coefficient3 * remainder5Coefficient3).natDegree ≤
        remainder5Coefficient3.natDegree + remainder5Coefficient3.natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 164 + 164 :=
      Nat.add_le_add recurrence4B3_natDegree_le
        recurrence4B3_natDegree_le

theorem recurrence4LeadingSquare_coeff_high (n : ℕ) (h : 328 < n) :
    recurrence4LeadingSquare.coeff n = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  exact lt_of_le_of_lt recurrence4LeadingSquare_natDegree_le h

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
