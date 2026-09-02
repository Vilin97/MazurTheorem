/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB3A3Part0
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB3A3Part1

/-!
# Recurrence 4 lookup certificate: B3A3 degree bound

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence4B3A3_natDegree_le :
    recurrence4B3A3.natDegree ≤ 346 := by
  unfold recurrence4B3A3
  calc
    (remainder5Coefficient3 * remainder4Coefficient3).natDegree ≤
        remainder5Coefficient3.natDegree + remainder4Coefficient3.natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 164 + 182 :=
      Nat.add_le_add recurrence4B3_natDegree_le
        recurrence4A3_natDegree_le

theorem recurrence4B3A3_coeff_high (n : ℕ) (h : 346 < n) :
    recurrence4B3A3.coeff n = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  exact lt_of_le_of_lt recurrence4B3A3_natDegree_le h

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
