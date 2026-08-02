/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.KummerArtinProduct

/-!
# Challenge: the global Kummer--Artin product formula

Mathlib already proves the ideal-local ramification criterion used by the
destination module, but it does not yet contain the required global Kummer
or Artin reciprocity theorem. This contract states the missing input as the
explicit finite product formula for the canonical Kummer presentation.

The checked destination API proves that this formula is equivalent to
conductor-one principal reciprocity and hence produces the required
surjective, inverse-cyclotomic ideal-class quotient. The separate
Herbrand--Kummer assertion that this quotient cannot exist is not part of
this contract.
-/

namespace MazurTheorem.Challenge

universe u

/-- Global Kummer reciprocity makes the finite product of local
Kummer/Frobenius symbols trivial on every principal fractional ideal. -/
theorem cyclotomic_kummerArtinProductFormulaPrinciple
    (p : ℕ) [Fact p.Prime] (_hp : 5 ≤ p) :
    NumberTheory.CyclotomicCharacter.KummerArtinProductFormulaPrinciple.{u} p := sorry

/-- Checked bridge from the exact Kummer product-formula contract to the
roadmap-facing class-field-theory principle. -/
theorem cyclotomic_classFieldTheoryPrinciple
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    NumberTheory.CyclotomicCharacter.ClassFieldTheoryPrinciple.{u} p :=
  NumberTheory.CyclotomicCharacter.classFieldTheoryPrinciple_of_kummerArtinProductFormula
    (cyclotomic_kummerArtinProductFormulaPrinciple p hp)

end MazurTheorem.Challenge
