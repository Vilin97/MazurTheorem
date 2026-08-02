/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.KummerArtinProduct

/-!
# Challenge: one-sided Kummer reciprocity for locally-primary pseudo-units

The destination proves that the canonical Kummer radicand has `p`-divisible
finite divisor and is a `p`-th power in the completion at the cyclotomic
prime. It also checks the comparison between Kummer/Frobenius coordinates,
clears prime-to-cyclotomic fractional denominators to integral ones, and
removes the cyclotomic-prime factor itself. The sole remaining arithmetic
contract is therefore integral one-sided Kummer reciprocity for a
locally-primary pseudo-unit.

The checked bridges then prove prime-to-cyclotomic and full principal
reciprocity, the Kummer product formula, and the required surjective
inverse-cyclotomic ideal-class quotient. The separate Herbrand--Kummer
assertion that this quotient cannot exist is not part of this contract.
-/

namespace MazurTheorem.Challenge

open NumberTheory.CyclotomicCharacter

universe u

/-- One-sided Kummer reciprocity kills every integral principal Kummer symbol
away from the cyclotomic prime when the radicand is a locally-primary
pseudo-unit. -/
theorem cyclotomic_locallyPrimaryPseudoUnitKummerReciprocityPrinciple
    (p : ℕ) [Fact p.Prime] (_hp : 5 ≤ p) :
    LocallyPrimaryPseudoUnitKummerReciprocityPrinciple.{u} p := sorry

/-- Checked reduction from the locally-primary pseudo-unit contract to
prime-to-cyclotomic principal Artin reciprocity. -/
theorem cyclotomic_primeToCyclotomicPrincipalReciprocityPrinciple
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    PrimeToCyclotomicPrincipalReciprocityPrinciple.{u} p :=
  primeToCyclotomicPrincipalReciprocityPrinciple_of_locallyPrimaryPseudoUnit
    (by omega)
    (cyclotomic_locallyPrimaryPseudoUnitKummerReciprocityPrinciple p hp)

/-- Checked reduction from prime-to-cyclotomic reciprocity to the full
Kummer product formula. -/
theorem cyclotomic_kummerArtinProductFormulaPrinciple
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    KummerArtinProductFormulaPrinciple.{u} p :=
  kummerArtinProductFormulaPrinciple_of_primeToCyclotomic
    (by omega)
    (cyclotomic_primeToCyclotomicPrincipalReciprocityPrinciple p hp)

/-- Checked bridge from the exact Kummer product-formula contract to the
roadmap-facing class-field-theory principle. -/
theorem cyclotomic_classFieldTheoryPrinciple
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    NumberTheory.CyclotomicCharacter.ClassFieldTheoryPrinciple.{u} p :=
  NumberTheory.CyclotomicCharacter.classFieldTheoryPrinciple_of_kummerArtinProductFormula
    (cyclotomic_kummerArtinProductFormulaPrinciple p hp)

end MazurTheorem.Challenge
