/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.CyclotomicPseudoUnitReciprocity

/-!
# Kummer coordinates for finite-prime Frobenius products

This file changes the cyclic coordinate of an inverse-cyclotomic extension
to the root-of-unity coordinate supplied by a Kummer presentation.  It then
extends the local Frobenius values to a finite product on nonzero fractional
ideals.  No principal product formula or reciprocity principle is asserted
here.
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

end NumberTheory.CyclotomicCharacter.InverseExtension
