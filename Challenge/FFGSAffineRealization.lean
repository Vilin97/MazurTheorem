/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.Affine

/-!
# Checked bridge: realize affine Hopf data as a geometric group scheme

The affine API constructs the internal commutative group object over `Spec R` and assembles its
scheme, point-group, and rank compatibility in `AffineFiniteFreePresentation`.  This file retains
the original contributor contract as a checked bridge.
-/

open AlgebraicGeometry

namespace MazurTheorem.Challenge

universe u

/-- Every finite-free commutative, cocommutative Hopf algebra has a compatible realization as a
finite-flat commutative group scheme over its affine base. -/
theorem affineFiniteFree_exists_geometric_realization
    {R : Type u} [CommRing R] (A : AffineFiniteFreeCommGroupScheme R) :
    ∃ (G : FiniteFlatCommGroupScheme (Spec (.of R)))
      (P : G.AffineFiniteFreePresentation), P.hopf = A := by
  exact AlgebraicGeometry.AffineFiniteFreeCommGroupScheme.exists_geometric_realization A

end MazurTheorem.Challenge
