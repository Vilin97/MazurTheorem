/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import TauCeti.AlgebraicGeometry.WeilDivisor.Principal.Basic
import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Degree
import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Order

/-!
# Challenge: the product formula on a smooth proper curve

This checked bridge preserves the exact residue-degree-weighted product-formula contract used by
the degree-zero Picard consumer.  Tau Ceti proves the result for its geometric order system; the
bridge transports it to an abstract order system with the same order homomorphisms.
-/

open AlgebraicGeometry

namespace MazurTheorem.Challenge

universe u

/-- The exact residue-degree-weighted product formula required to transport divisor degree zero
to the scheme Picard group. The equality `hord` pins the abstract order system to Mathlib's
geometric orders of vanishing. -/
theorem divisorProductFormula
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (π : X ⟶ Spec (.of K)) [IsProper π] [SmoothOfRelativeDimension 1 π]
    (S : TauCeti.AlgebraicGeometry.WeilDivisor.OrderSystem
      (TauCeti.AlgebraicGeometry.CodimensionOnePoint X)
      (Additive X.functionFieldˣ))
    (hord : S.ord = TauCeti.AlgebraicGeometry.SchemeWeilDivisor.orderAt) :
    S.IsWeightedDegreeZero (fun x ↦ (π.residueDegree x : ℤ)) := by
  exact
    TauCeti.AlgebraicGeometry.SchemeWeilDivisor.isWeightedDegreeZero_of_ord_eq_orderAt
      π S hord
      (TauCeti.AlgebraicGeometry.SchemeWeilDivisor.orderSystem_isWeightedDegreeZero K X π)

end MazurTheorem.Challenge
