/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module

public import TauCeti.AlgebraicGeometry.AbelianVariety.Product

/-!
# Dimension of a product of abelian varieties

This is a small acceptance theorem for Tau Ceti's abelian-variety product
API. It is useful preparation for powers of Jacobians, but it is not itself a
proof of any Mazur endpoint.
-/

public section

namespace MazurTauCetiChallenge

open TauCeti.AlgebraicGeometry

universe u

/-- The dimension of a product of abelian varieties is the sum of the
dimensions. -/
theorem prod_dim {K : Type u} [Field K] (A B : AbelianVariety K) :
    (AbelianVariety.prod A B).dim = A.dim + B.dim := sorry

/-- The self-product of an abelian variety has twice its dimension. -/
theorem prod_self_dim {K : Type u} [Field K] (A : AbelianVariety K) :
    (AbelianVariety.prod A A).dim = 2 * A.dim := by
  simpa [two_mul] using prod_dim A A

end MazurTauCetiChallenge
