/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.CyclotomicKummer

/-!
# Kummer coordinates for the finite-prime Artin product

This file rewrites the ideal-theoretic Artin map of an inverse-cyclotomic
extension in the Kummer pairing attached to a chosen radical.  The resulting
principal product formula is proved equivalent, without an arithmetic
assumption, to conductor-one principal reciprocity for the original Artin
map.  The genuinely global assertion is then isolated as a named principle.
-/

open scoped NumberField nonZeroDivisors

namespace NumberTheory.CyclotomicCharacter.InverseExtension

universe u

variable {p : ℕ} [Fact p.Prime]
variable {L : Type u} [Field L] [NumberField L]
variable [Algebra (PrimeCyclotomicField p) L]
variable [IsScalarTower ℚ (PrimeCyclotomicField p) L]

/-- Change from the cyclic coordinate packaged in an inverse extension to
the root-of-unity coordinate supplied by a Kummer presentation. -/
noncomputable def KummerPresentation.coordinateEquiv
    (E : InverseExtension p L) (P : KummerPresentation E) :
    Multiplicative (ZMod p) ≃*
      rootsOfUnity p (PrimeCyclotomicField p) :=
  E.galEquiv.symm.trans (P.pairing E)

/-- The local arithmetic Frobenius symbol in the Kummer root-of-unity
coordinate. -/
noncomputable def KummerPresentation.localKummerFrobeniusSymbol
    (E : InverseExtension p L) (P : KummerPresentation E)
    (v : FinitePrime (PrimeCyclotomicField p)) :
    rootsOfUnity p (PrimeCyclotomicField p) :=
  P.coordinateEquiv E (E.artinSymbol v)

/-- The local Kummer symbol is the Kummer pairing evaluated on the selected
arithmetic Frobenius automorphism. -/
theorem KummerPresentation.localKummerFrobeniusSymbol_eq_pairing
    (E : InverseExtension p L) (P : KummerPresentation E)
    (v : FinitePrime (PrimeCyclotomicField p)) :
    P.localKummerFrobeniusSymbol E v =
      P.pairing E (E.frobeniusAt v) := by
  simp only [localKummerFrobeniusSymbol, coordinateEquiv,
    artinSymbol, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]

/-- Extend the local Kummer/Frobenius symbols to nonzero fractional ideals.
By construction this is the finite product over the prime divisor of the
fractional ideal. -/
noncomputable def KummerPresentation.fractionalKummerSymbol
    (E : InverseExtension p L) (P : KummerPresentation E) :
    (FractionalIdeal
      (nonZeroDivisors
        (NumberField.RingOfIntegers (PrimeCyclotomicField p)))
      (PrimeCyclotomicField p))ˣ →*
        rootsOfUnity p (PrimeCyclotomicField p) :=
  NumberTheory.UnramifiedArtin.fractionalIdealHom
    (P.localKummerFrobeniusSymbol E)

/-- On a prime fractional ideal, the finite product is the corresponding
local Kummer/Frobenius symbol. -/
@[simp]
theorem KummerPresentation.fractionalKummerSymbol_prime
    (E : InverseExtension p L) (P : KummerPresentation E)
    (v : FinitePrime (PrimeCyclotomicField p)) :
    P.fractionalKummerSymbol E
      (NumberTheory.UnramifiedArtin.primeFractionalIdealUnit
        (K := PrimeCyclotomicField p) v) =
      P.localKummerFrobeniusSymbol E v :=
  NumberTheory.UnramifiedArtin.fractionalIdealHom_prime _ v

/-- Explicit finite-product formula for a fractional Kummer symbol. -/
theorem KummerPresentation.fractionalKummerSymbol_apply
    (E : InverseExtension p L) (P : KummerPresentation E)
    (I : (FractionalIdeal
      (nonZeroDivisors
        (NumberField.RingOfIntegers (PrimeCyclotomicField p)))
      (PrimeCyclotomicField p))ˣ) :
    P.fractionalKummerSymbol E I =
      (NumberTheory.UnramifiedArtin.fractionalIdealDivisor
        (NumberField.RingOfIntegers (PrimeCyclotomicField p))
        (PrimeCyclotomicField p) (Additive.ofMul I)).prod
        (fun v n => (P.localKummerFrobeniusSymbol E v) ^ n) :=
  NumberTheory.UnramifiedArtin.fractionalIdealHom_apply _ I

/-- The fractional Kummer symbol is exactly the original fractional Artin
map followed by the change to Kummer coordinates. -/
theorem KummerPresentation.fractionalKummerSymbol_eq_coordinate_comp
    (E : InverseExtension p L) (P : KummerPresentation E) :
    P.fractionalKummerSymbol E =
      (P.coordinateEquiv E).toMonoidHom.comp E.fractionalArtin := by
  change NumberTheory.UnramifiedArtin.fractionalIdealHom
      (fun v => P.coordinateEquiv E (E.artinSymbol v)) =
    (P.coordinateEquiv E).toMonoidHom.comp
      (NumberTheory.UnramifiedArtin.fractionalIdealHom E.artinSymbol)
  exact (NumberTheory.UnramifiedArtin.fractionalIdealHom_comp
    (P.coordinateEquiv E).toMonoidHom E.artinSymbol).symm

/-- The exact principal product formula in Kummer coordinates: the finite
product of local Kummer/Frobenius symbols attached to every principal
fractional ideal is one. -/
def KummerPresentation.SatisfiesPrincipalProductFormula
    (E : InverseExtension p L) (P : KummerPresentation E) : Prop :=
  ∀ x : (PrimeCyclotomicField p)ˣ,
    (NumberTheory.UnramifiedArtin.fractionalIdealDivisor
      (NumberField.RingOfIntegers (PrimeCyclotomicField p))
      (PrimeCyclotomicField p)
      (Additive.ofMul
        (toPrincipalIdeal
          (NumberField.RingOfIntegers (PrimeCyclotomicField p))
          (PrimeCyclotomicField p) x))).prod
      (fun v n => (P.localKummerFrobeniusSymbol E v) ^ n) = 1

/-- The explicit product formula is the statement that the fractional
Kummer-symbol homomorphism kills principal ideals. -/
theorem KummerPresentation.satisfiesPrincipalProductFormula_iff_kills
    (E : InverseExtension p L) (P : KummerPresentation E) :
    P.SatisfiesPrincipalProductFormula E ↔
      NumberTheory.UnramifiedArtin.KillsPrincipalIdeals
        (NumberField.RingOfIntegers (PrimeCyclotomicField p))
        (PrimeCyclotomicField p) (P.fractionalKummerSymbol E) := by
  constructor
  · intro h x
    rw [P.fractionalKummerSymbol_apply E]
    exact h x
  · intro h x
    rw [← P.fractionalKummerSymbol_apply E]
    exact h x

/-- Changing from cyclic coordinates to Kummer coordinates preserves and
reflects the property of killing all principal fractional ideals. -/
theorem KummerPresentation.killsPrincipalKummerSymbols_iff_reciprocity
    (E : InverseExtension p L) (P : KummerPresentation E) :
    NumberTheory.UnramifiedArtin.KillsPrincipalIdeals
        (NumberField.RingOfIntegers (PrimeCyclotomicField p))
        (PrimeCyclotomicField p) (P.fractionalKummerSymbol E) ↔
      E.SatisfiesPrincipalReciprocity := by
  rw [P.fractionalKummerSymbol_eq_coordinate_comp E]
  constructor
  · intro h x
    apply (P.coordinateEquiv E).injective
    change P.coordinateEquiv E
        (E.fractionalArtin
          (toPrincipalIdeal
            (NumberField.RingOfIntegers (PrimeCyclotomicField p))
            (PrimeCyclotomicField p) x)) =
      P.coordinateEquiv E 1
    simpa using h x
  · intro h x
    change P.coordinateEquiv E
        (E.fractionalArtin
          (toPrincipalIdeal
            (NumberField.RingOfIntegers (PrimeCyclotomicField p))
            (PrimeCyclotomicField p) x)) = 1
    rw [h x, map_one]

/-- The Kummer principal product formula is an exact reformulation of
conductor-one principal reciprocity for the ideal Artin map. -/
theorem KummerPresentation.satisfiesPrincipalProductFormula_iff_reciprocity
    (E : InverseExtension p L) (P : KummerPresentation E) :
    P.SatisfiesPrincipalProductFormula E ↔
      E.SatisfiesPrincipalReciprocity :=
  (P.satisfiesPrincipalProductFormula_iff_kills E).trans
    (P.killsPrincipalKummerSymbols_iff_reciprocity E)

end NumberTheory.CyclotomicCharacter.InverseExtension

namespace NumberTheory.CyclotomicCharacter

universe u

/-- The missing global product formula, stated in the canonical Kummer
presentation of every everywhere-finite-unramified inverse extension. -/
def KummerArtinProductFormulaPrinciple
    (p : ℕ) [Fact p.Prime] : Prop :=
  NumberField.IsTotallyComplex (PrimeCyclotomicField p) →
    ∀ {L : Type u} [Field L] [NumberField L]
      [Algebra (PrimeCyclotomicField p) L]
      [IsScalarTower ℚ (PrimeCyclotomicField p) L]
      (E : InverseExtension p L),
      E.IsUnramifiedAtFinitePlaces →
        E.kummerPresentation.SatisfiesPrincipalProductFormula E

/-- The global Kummer product formula supplies conductor-one principal
reciprocity for every relevant inverse extension. -/
theorem principalReciprocityPrinciple_of_kummerArtinProductFormula
    {p : ℕ} [Fact p.Prime]
    (hproduct : KummerArtinProductFormulaPrinciple.{u} p) :
    PrincipalReciprocityPrinciple.{u} p := by
  intro hcomplex L _ _ _ _ E hunramified
  exact (E.kummerPresentation.satisfiesPrincipalProductFormula_iff_reciprocity E).mp
      (hproduct hcomplex E hunramified)

/-- Consequently, the global Kummer product formula gives the class-group
quotient required by the cyclotomic obstruction. -/
theorem classFieldTheoryPrinciple_of_kummerArtinProductFormula
    {p : ℕ} [Fact p.Prime]
    (hproduct : KummerArtinProductFormulaPrinciple.{u} p) :
    ClassFieldTheoryPrinciple.{u} p :=
  classFieldTheoryPrinciple_of_principalReciprocity
    (principalReciprocityPrinciple_of_kummerArtinProductFormula hproduct)

end NumberTheory.CyclotomicCharacter
