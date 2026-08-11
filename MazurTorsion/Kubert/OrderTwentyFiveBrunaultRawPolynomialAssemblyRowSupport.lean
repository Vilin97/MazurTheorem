/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialAssemblyData
import MazurTorsion.Kubert.OrderTwentyFiveDensePolynomialRowCertificate
import Mathlib.Data.List.GetD

/-!
# Support lemmas for raw numerator assembly rows

The row certificates compare only the genuine support of each row.  This
leaf turns those bounded coefficient equalities into equality after padding,
with every later coefficient discharged structurally as a list default.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

open OrderTwentyFiveDensePolynomial
open OrderTwentyFiveDensePolynomialRectangular
open OrderTwentyFiveDensePolynomialRowCertificate

/-- Exact outer support of the dense eleven-term assembly. -/
theorem assemblyData_outerSupport : assemblyData.length = 83 := by
  decide

/-- Two rows with a common support bound and equal supported coefficients
remain equal after padding to any larger width. -/
theorem padOne_eq_of_bounded_coefficients
    (inner support : ℕ) (p q : One)
    (hp : p.length ≤ support) (hq : q.length ≤ support)
    (hsi : support ≤ inner)
    (hc : ∀ j, j < support → p.getD j 0 = q.getD j 0) :
    padOne inner p = padOne inner q := by
  apply padOne_eq_of_coefficients inner p (padOne inner q)
    (hp.trans hsi)
  · simp only [padOne, List.length_append, List.length_replicate]
    omega
  · intro j hj
    rw [getD_padOne inner q j hj]
    by_cases hjs : j < support
    · exact hc j hjs
    · rw [List.getD_eq_default _ _ (by omega),
          List.getD_eq_default _ _ (by omega)]

end MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal
