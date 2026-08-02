/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.CyclotomicUnramified
import MazurTorsion.Upstream.AINTLIB.FltRegular.NumberTheory.Hilbert94

/-!
# Hilbert 94 for inverse-cyclotomic extensions

This module specializes the checked AINTLIB Hilbert-94 port to an
`InverseExtension`.  Everywhere finite-place unramifiedness forces the prime
degree to divide the class number of the cyclotomic base.

This is deliberately a non-equivariant obstruction: divisibility of the
whole class number does not identify the inverse-cyclotomic eigenspace.
-/

open scoped NumberField

namespace NumberTheory.CyclotomicCharacter.InverseExtension

universe u

/-- An everywhere finite-place unramified inverse extension of odd prime
degree forces that prime to divide the class number of the cyclotomic base.

This is the honest non-equivariant consequence of Hilbert 94; it does not
select a character component of the class group. -/
theorem prime_dvd_card_classGroup_of_isUnramifiedAtFinitePlaces
    {p : ℕ} [Fact p.Prime] (hp : 2 < p)
    {L : Type u} [Field L] [NumberField L]
    [Algebra (PrimeCyclotomicField p) L]
    [IsScalarTower ℚ (PrimeCyclotomicField p) L]
    (E : InverseExtension p L) (hunramified : E.IsUnramifiedAtFinitePlaces) :
    p ∣ Fintype.card
      (ClassGroup (NumberField.RingOfIntegers (PrimeCyclotomicField p))) := by
  letI : IsGalois (PrimeCyclotomicField p) L := E.isGalois
  letI : Algebra.Unramified
      (NumberField.RingOfIntegers (PrimeCyclotomicField p))
      (NumberField.RingOfIntegers L) :=
    E.algebraUnramified_iff_isUnramifiedAtFinitePlaces.mpr hunramified
  letI : IsCyclic Gal(L/PrimeCyclotomicField p) :=
    isCyclic_of_surjective E.galEquiv.symm.toMonoidHom E.galEquiv.symm.surjective
  have hfinrank : Module.finrank (PrimeCyclotomicField p) L = p := by
    calc
      Module.finrank (PrimeCyclotomicField p) L =
          Nat.card Gal(L/PrimeCyclotomicField p) :=
        (IsGalois.card_aut_eq_finrank (PrimeCyclotomicField p) L).symm
      _ = Nat.card (Multiplicative (ZMod p)) :=
        Nat.card_congr E.galEquiv.toEquiv
      _ = p := by simp
  have hprime : Nat.Prime (Module.finrank (PrimeCyclotomicField p) L) := by
    rw [hfinrank]
    exact Fact.out
  have hne_two : Module.finrank (PrimeCyclotomicField p) L ≠ 2 := by
    rw [hfinrank]
    omega
  simpa only [hfinrank] using
    (dvd_card_classGroup_of_unramified_isCyclic
      (K := PrimeCyclotomicField p) (L := L) hprime hne_two)

/-- Hilbert 94 therefore produces an abstract cyclic order-`p` quotient of
the cyclotomic class group.  This still records no cyclotomic Galois
character; upgrading it to `InverseClassGroupQuotient` is precisely the
remaining equivariant reciprocity step. -/
theorem nonempty_unramifiedClassGroupQuotient_of_isUnramifiedAtFinitePlaces
    {p : ℕ} [Fact p.Prime] (hp : 2 < p)
    {L : Type u} [Field L] [NumberField L]
    [Algebra (PrimeCyclotomicField p) L]
    [IsScalarTower ℚ (PrimeCyclotomicField p) L]
    (E : InverseExtension p L) (hunramified : E.IsUnramifiedAtFinitePlaces) :
    Nonempty (UnramifiedClassGroupQuotient p) :=
  nonempty_unramifiedClassGroupQuotient_iff_prime_dvd_card.mpr (by
    simpa using
      E.prime_dvd_card_classGroup_of_isUnramifiedAtFinitePlaces hp hunramified)

end NumberTheory.CyclotomicCharacter.InverseExtension
