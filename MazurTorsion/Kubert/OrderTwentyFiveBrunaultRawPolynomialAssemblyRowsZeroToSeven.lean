/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialAssemblyRowsZeroToFive
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialAssemblyRowSix
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialAssemblyRowSeven

/-!
# Rows zero through seven of the raw numerator assembly certificate

This facade collects the first eight complete, tail-safe row equalities.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

open OrderTwentyFiveDensePolynomialRectangular

/-- The first eight rows of the checked raw numerator assembly. -/
theorem assemblyRowsZeroToSeven_spec (n : ℕ) (hn : n < 8) :
    (rectangularize 83 121 assemblyData).getD n [] =
      (rectangularize 83 121 divisionReducedData).getD n [] := by
  interval_cases n
  · exact assemblyRow0
  · exact assemblyRow1
  · exact assemblyRow2
  · exact assemblyRow3
  · exact assemblyRow4
  · exact assemblyRow5
  · exact assemblyRow6
  · exact assemblyRow7

end MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal
