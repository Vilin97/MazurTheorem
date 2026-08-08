/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.Data.ZMod.Basic

/-!
# The genus-four Brunault model for order twenty-five

Brunault records the following affine equation for the genus-four quotient
`X₁(25) / ⟨7⟩`, in modular-unit coordinates `u,v`:

`v²u⁴ + (v³+v²)u³ + (3v³-v²-2v)u² + (v⁴-4v²+v-1)u - v³ = 0`.

This file defines the polynomial over an arbitrary commutative ring and checks
its affine reduction modulo three.  The only affine zero over `ZMod 3` is the
boundary point `(0,0)`.  This finite computation does not classify rational
points on the genus-four curve or construct its normalization.

The equation is from François Brunault, *On the Mahler measure associated to
`X₁(13)`*, §6.3.  The characteristic-zero comparison with the Tate-normal
order-twenty-five model is developed in the downstream Brunault bridge.
-/

namespace MazurTorsion.Kubert

/-- Brunault's affine polynomial for the genus-four quotient of `X₁(25)`. -/
def orderTwentyFiveBrunaultPolynomial
    {R : Type*} [CommRing R] (u v : R) : R :=
  v ^ 2 * u ^ 4 + (v ^ 3 + v ^ 2) * u ^ 3 +
    (3 * v ^ 3 - v ^ 2 - 2 * v) * u ^ 2 +
    (v ^ 4 - 4 * v ^ 2 + v - 1) * u - v ^ 3

/-- The only affine zero of Brunault's model over `F₃` is the boundary point
`(0,0)`. -/
theorem orderTwentyFiveBrunaultPolynomial_f3_eq_zero_iff
    (u v : ZMod 3) :
    orderTwentyFiveBrunaultPolynomial u v = 0 ↔
      u = 0 ∧ v = 0 := by
  decide +revert

/-- A point of the nonzero modular-unit chart cannot reduce to an affine zero
of Brunault's model over `F₃`.  This is the named downstream consumer of the
complete affine enumeration. -/
theorem orderTwentyFiveBrunaultPolynomial_f3_ne_zero_of_open
    (u v : ZMod 3) (hopen : u ≠ 0 ∧ v ≠ 0) :
    orderTwentyFiveBrunaultPolynomial u v ≠ 0 := by
  intro hzero
  obtain ⟨hu0, hv0⟩ :=
    (orderTwentyFiveBrunaultPolynomial_f3_eq_zero_iff u v).mp hzero
  exact hopen.1 hu0

end MazurTorsion.Kubert
