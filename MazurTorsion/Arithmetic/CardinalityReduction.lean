/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Arithmetic.LowTorsionObstructions
import MazurTorsion.GroupTheory.FiniteClassification

/-!
# Numerical reduction for rational elliptic-curve torsion

The generic finite-abelian theorem proves the numerical bound directly from allowed element
orders and seven forbidden embeddings. Three of those embeddings are already excluded by the
compiled `2`-, `3`-, and `4`-torsion arguments. This file specializes the generic theorem and
exposes the exact four remaining subgroup exclusions.

The final proof splits on finiteness of the torsion set. This is not a workaround: `Set.ncard`
is definitionally zero on infinite sets, so no Mordell--Weil finiteness input is needed for the
literal LeanPool statement.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion

variable (E : WeierstrassCurve ℚ)

/-- The seven forbidden-embedding inputs for rational torsion, with the `2`-, `3`-, and
`4`-primary fields discharged by the compiled coordinate arguments. -/
theorem rationalTorsionAvoidsMazurForbiddenSubgroups
    (h55 : ForbidsEmbedding (ZMod 5 × ZMod 5) (RationalTorsion E))
    (h77 : ForbidsEmbedding (ZMod 7 × ZMod 7) (RationalTorsion E))
    (h210 : ForbidsEmbedding (ZMod 2 × ZMod 10) (RationalTorsion E))
    (h212 : ForbidsEmbedding (ZMod 2 × ZMod 12) (RationalTorsion E)) :
    AvoidsMazurForbiddenSubgroups (RationalTorsion E) :=
  { c2Cube := rationalTorsion_forbids_zmod_two_cube E
    c3Square := rationalTorsion_forbids_zmod_three_square E
    c4Square := rationalTorsion_forbids_zmod_four_square E
    c5Square := h55
    c7Square := h77
    c2c10 := h210
    c2c12 := h212 }

/-- Exact LeanPool cardinality target reduced to the rational point-order theorem, full rational
`5`- and `7`-torsion obstructions, and the two exceptional product obstructions. -/
theorem torsion_ncard_le_of_arithmetic_inputs
    (horders : ∀ x : RationalTorsion E, addOrderOf x ∈ cyclicOrders)
    (h55 : ForbidsEmbedding (ZMod 5 × ZMod 5) (RationalTorsion E))
    (h77 : ForbidsEmbedding (ZMod 7 × ZMod 7) (RationalTorsion E))
    (h210 : ForbidsEmbedding (ZMod 2 × ZMod 10) (RationalTorsion E))
    (h212 : ForbidsEmbedding (ZMod 2 × ZMod 12) (RationalTorsion E)) :
    (AddCommGroup.torsion (E⁄ℚ).Point : Set (E⁄ℚ).Point).ncard ≤ 16 := by
  rcases (AddCommGroup.torsion (E⁄ℚ).Point : Set (E⁄ℚ).Point).finite_or_infinite with
    hfinite | hinfinite
  · letI : Fintype (RationalTorsion E) := hfinite.fintype
    change Nat.card (RationalTorsion E) ≤ 16
    exact card_le_sixteen_of_allowed_orders_and_forbidden horders <|
      rationalTorsionAvoidsMazurForbiddenSubgroups E h55 h77 h210 h212
  · rw [hinfinite.ncard]
    omega

end MazurTorsion
