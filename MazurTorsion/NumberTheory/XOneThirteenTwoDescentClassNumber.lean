/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenTwoDescentDiscriminant
import MazurTorsion.NumberTheory.XOneThirteenTwoDescentInertia

/-!
# Class number one for the `X₁(13)` two-descent field

The checked alternate power basis bounds the maximal-order discriminant by
`10816`.  The independent small-prime inertia certificates then discharge
the finite Minkowski calculation, giving class number one unconditionally.
-/

namespace MazurTorsion.XOneThirteenTwoDescentClassNumber

open Polynomial
open XOneThirteenTwoDescentSextic

noncomputable section

local instance : Fact (Irreducible rationalSextic) :=
  ⟨rationalSextic_irreducible⟩

/-- The sextic field used by the `X₁(13)` two-descent has class number
one. -/
theorem sexticField_classNumber_eq_one :
    NumberField.classNumber SexticField = 1 :=
  XOneThirteenTwoDescentInertia.classNumber_eq_one_of_discr_le
    XOneThirteenTwoDescentDiscriminant.sexticField_discr_abs_le

end

end MazurTorsion.XOneThirteenTwoDescentClassNumber
