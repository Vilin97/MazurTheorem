/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.Affine

/-!
# Challenge: realize affine Hopf data as a geometric group scheme

The compiled affine API identifies geometric affine points with convolution points.  What remains
is the categorical construction of the corresponding internal commutative group object over
`Spec R`, together with the scheme, point-group, and rank compatibility assembled in
`AffineFiniteFreePresentation`.
-/

open AlgebraicGeometry

namespace MazurTheorem.Challenge

universe u

/-- Every finite-free commutative, cocommutative Hopf algebra has a compatible realization as a
finite-flat commutative group scheme over its affine base. -/
theorem affineFiniteFree_exists_geometric_realization
    {R : Type u} [CommRing R] (A : AffineFiniteFreeCommGroupScheme R) :
    ∃ (G : FiniteFlatCommGroupScheme (Spec (.of R)))
      (P : G.AffineFiniteFreePresentation), P.hopf = A := sorry

end MazurTheorem.Challenge
