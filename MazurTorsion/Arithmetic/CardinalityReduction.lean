/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Arithmetic.LowTorsionObstructions
import MazurTorsion.Arithmetic.ExceptionalProducts
import MazurTorsion.Arithmetic.OddPrimeObstructions
import MazurTorsion.GroupTheory.FiniteClassification

/-!
# Numerical reduction for rational elliptic-curve torsion

The generic finite-abelian theorem proves the numerical bound directly from allowed element
orders and seven forbidden embeddings.  All seven embeddings are excluded by the compiled
low-level, odd-prime, two-descent, quartic-descent, and good-reduction arguments.  This file
specializes the generic theorem and leaves only the rational point-order classification as an
input.

The final proof splits on finiteness of the torsion set. This is not a workaround: `Set.ncard`
is definitionally zero on infinite sets, so no Mordell--Weil finiteness input is needed for the
literal LeanPool statement.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion

variable (E : WeierstrassCurve ℚ)

/-- The seven forbidden embeddings are all excluded for rational torsion. -/
theorem rationalTorsionAvoidsMazurForbiddenSubgroups
    [E.IsElliptic] :
    AvoidsMazurForbiddenSubgroups (RationalTorsion E) :=
  { c2Cube := rationalTorsion_forbids_zmod_two_cube E
    c3Square := rationalTorsion_forbids_zmod_three_square E
    c4Square := rationalTorsion_forbids_zmod_four_square E
    c5Square := rationalTorsion_forbids_zmod_five_square E
    c7Square := rationalTorsion_forbids_zmod_seven_square E
    c2c10 := rationalTorsion_forbids_zmod_two_prod_ten E
    c2c12 := rationalTorsion_forbids_zmod_two_prod_twelve E }

/-- Exact LeanPool cardinality target reduced to the rational point-order theorem. -/
theorem torsion_ncard_le_of_arithmetic_inputs
    [E.IsElliptic]
    (horders : ∀ x : RationalTorsion E, addOrderOf x ∈ cyclicOrders) :
    (AddCommGroup.torsion (E⁄ℚ).Point : Set (E⁄ℚ).Point).ncard ≤ 16 := by
  rcases (AddCommGroup.torsion (E⁄ℚ).Point : Set (E⁄ℚ).Point).finite_or_infinite with
    hfinite | hinfinite
  · letI : Fintype (RationalTorsion E) := hfinite.fintype
    change Nat.card (RationalTorsion E) ≤ 16
    exact card_le_sixteen_of_allowed_orders_and_forbidden horders <|
      rationalTorsionAvoidsMazurForbiddenSubgroups E
  · rw [hinfinite.ncard]
    omega

/-- Alias emphasizing that all subgroup and exceptional-curve inputs are
discharged internally. -/
theorem torsion_ncard_le_of_explicit_arithmetic
    [E.IsElliptic]
    (horders : ∀ x : RationalTorsion E, addOrderOf x ∈ cyclicOrders) :
    (AddCommGroup.torsion (E⁄ℚ).Point : Set (E⁄ℚ).Point).ncard ≤ 16 :=
  torsion_ncard_le_of_arithmetic_inputs E horders

end MazurTorsion
