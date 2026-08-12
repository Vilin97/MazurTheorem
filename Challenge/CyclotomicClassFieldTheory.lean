/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.CyclotomicUnramified

/-!
# Challenge: the unramified class-field quotient

Mathlib already proves the ideal-local ramification criterion used by the
destination module, but it does not yet contain the Hilbert class field or
global Artin reciprocity.  This contract is exactly that missing global step.

Its conclusion is deliberately structured: an everywhere finite-place
unramified inverse-cyclotomic extension must yield a surjective quotient of
the ideal class group by `Multiplicative (ZMod p)`, and that quotient must be
equivariant for the inverse cyclotomic character.  The separate
Herbrand--Kummer assertion that this eigenspace vanishes is not part of this
contract.
-/

namespace MazurTheorem.Challenge

universe u

/-- Global class field theory sends every everywhere-unramified
inverse-cyclotomic extension to the corresponding inverse-character quotient
of the cyclotomic ideal class group. -/
theorem cyclotomic_classFieldTheoryPrinciple
    (p : ℕ) [Fact p.Prime] (_hp : 5 ≤ p) :
    NumberTheory.CyclotomicCharacter.ClassFieldTheoryPrinciple.{u} p := sorry

end MazurTheorem.Challenge
