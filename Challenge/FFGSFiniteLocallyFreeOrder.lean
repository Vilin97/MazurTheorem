/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.Affine

/-!
# Checked bridge: descend the affine order theorem

The affine API localizes a point and its convolution powers, applies the finite-free theorem over
each local ring, and descends the equality.  The explicit constant-rank hypothesis remains
essential on a disconnected base.  This file retains the original contract as a checked bridge.
-/

noncomputable section

open CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open AlgebraicGeometry

namespace MazurTheorem.Challenge

universe u

/-- A point of an affine finite-flat commutative group scheme of constant rank `n` is killed by
`n`, without assuming that its coordinate module is globally free. -/
theorem affineFiniteFlat_point_pow_eq_one_of_constantRank
    {R : Type u} [CommRing R]
    (G : AffineFiniteFlatCommGroupScheme R) (n : ℕ)
    (hG : ∀ s : Spec (.of R), G.structureMap.finrank s = n)
    (B : Type u) [CommRing B] [Algebra R B]
    (x : G.Point B) :
    x ^ n = 1 :=
  AlgebraicGeometry.AffineFiniteFlatCommGroupScheme.point_pow_eq_one_of_constantRank
    G n hG B x

end MazurTheorem.Challenge
