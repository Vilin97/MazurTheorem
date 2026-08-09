/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.CyclotomicKummerResidueProduct
import MazurTorsion.NumberTheory.CyclotomicLocalPrimaryCongruence

/-!
# Local primary data after pseudo-unit normalization

This file transports an actual `p`-th root in the cyclotomic-prime
completion across a change of Kummer radicand by a `p`-th power.  For an
integral normalized radicand coprime to the cyclotomic prime, the transported
root supplies the finite-primary congruence used by one-sided reciprocity.
-/

open scoped NumberField nonZeroDivisors

namespace NumberTheory.CyclotomicCharacter.InverseExtension

universe u

variable {p : ℕ} [Fact p.Prime]
variable {L : Type u} [Field L] [NumberField L]
variable [Algebra (PrimeCyclotomicField p) L]
variable [IsScalarTower ℚ (PrimeCyclotomicField p) L]

/-- A local `p`-th root of a Kummer radicand remains a local `p`-th root
after multiplying the radicand by the `p`-th power used in an integral
normalization.  Consequently, a normalized numerator avoiding the
cyclotomic prime is finite-primary. -/
theorem KummerPresentation.isFinitePrimaryAtCyclotomicPrime_of_localRoot_normalization
    (E : InverseExtension p L) (P : KummerPresentation E)
    (hlocal : ∃ y : (cyclotomicPrime p).adicCompletion
        (PrimeCyclotomicField p),
      y ^ p = algebraMap (PrimeCyclotomicField p)
        ((cyclotomicPrime p).adicCompletion (PrimeCyclotomicField p))
        P.radicand)
    (η : NumberField.RingOfIntegers (PrimeCyclotomicField p))
    (c : (PrimeCyclotomicField p)ˣ)
    (hη : algebraMap
      (NumberField.RingOfIntegers (PrimeCyclotomicField p))
      (PrimeCyclotomicField p) η =
        P.radicand * (c : PrimeCyclotomicField p) ^ p)
    (hηPrime : η ∉ (cyclotomicPrime p).asIdeal) :
    IsFinitePrimaryAtCyclotomicPrime η := by
  apply isFinitePrimaryAtCyclotomicPrime_of_adic_pthPower η hηPrime
  obtain ⟨y, hy⟩ := hlocal
  refine ⟨y * algebraMap (PrimeCyclotomicField p)
    ((cyclotomicPrime p).adicCompletion (PrimeCyclotomicField p))
      (c : PrimeCyclotomicField p), ?_⟩
  rw [mul_pow, hy, ← map_pow, ← map_mul, ← hη]
  exact (IsScalarTower.algebraMap_apply
    (NumberField.RingOfIntegers (PrimeCyclotomicField p))
    (PrimeCyclotomicField p)
    ((cyclotomicPrime p).adicCompletion (PrimeCyclotomicField p)) η).symm

end NumberTheory.CyclotomicCharacter.InverseExtension
