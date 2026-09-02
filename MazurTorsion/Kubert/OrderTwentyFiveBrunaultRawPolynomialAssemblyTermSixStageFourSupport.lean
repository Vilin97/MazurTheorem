/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialAssemblyTermSixData
import MazurTorsion.Kubert.OrderTwentyFiveDensePolynomialRowCertificate
import MazurTorsion.Kubert.OrderTwentyFiveDensePolynomialSupport

/-!
# Structural support for the fourth stage of the sixth assembly term
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

open OrderTwentyFiveDensePolynomial
open OrderTwentyFiveDensePolynomialRowCertificate
open OrderTwentyFiveDensePolynomialSupport

private theorem v3Data_innerSupport : HasInnerSupport 67 V3Data :=
  hasInnerSupport_of_check (by decide)

/-- The exact inner support used to expose bounded coefficient windows in the
fourth multiplication stage. -/
theorem term6Stage4_v3Data_innerSupport : HasInnerSupport 67 V3Data :=
  v3Data_innerSupport

private theorem term6Stage3Data_innerSupport :
    HasInnerSupport 27 Term6Stage3Data :=
  hasInnerSupport_of_check (by decide)

private theorem term6Stage4Data_innerSupport :
    HasInnerSupport 93 Term6Stage4Data :=
  hasInnerSupport_of_check (by decide)

theorem term6Stage4_mulRow_length_le (n : ℕ) :
    (mulRow V3Data Term6Stage3Data n).length ≤ 93 := by
  rw [mulRow_eq_getD]
  exact getD_length_le
    (hasInnerSupport_mul 67 27 V3Data Term6Stage3Data
      v3Data_innerSupport term6Stage3Data_innerSupport) n

theorem term6Stage4Data_row_length_le (n : ℕ) :
    (Term6Stage4Data.getD n []).length ≤ 93 :=
  getD_length_le term6Stage4Data_innerSupport n

end MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal
