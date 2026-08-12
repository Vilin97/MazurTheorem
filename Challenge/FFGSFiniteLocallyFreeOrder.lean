/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.Affine

/-!
# Challenge: descend the affine order theorem

The local-base theorem is compiled.  The remaining global step is to localize a point and its
convolution powers, apply the finite-free theorem over each local ring, and descend the equality.
The explicit constant-rank hypothesis is essential on a disconnected base.
-/

open AlgebraicGeometry

namespace MazurTheorem.Challenge

universe u

/-- A point of an affine finite-flat commutative group scheme of constant rank `n` is killed by
`n`, without assuming that its coordinate module is globally free. -/
theorem affineFiniteFlat_point_pow_eq_one_of_constantRank
    {R : Type u} [CommRing R] [Nontrivial R]
    (G : AffineFiniteFlatCommGroupScheme R) (n : ℕ)
    (hG : ∀ s : Spec (.of R), G.structureMap.finrank s = n)
    (B : Type u) [CommRing B] [Algebra R B] [Nontrivial B]
    (x : G.Point B) :
    x ^ n = 1 := sorry

end MazurTheorem.Challenge
