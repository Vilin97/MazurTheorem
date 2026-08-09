/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.CyclotomicKummerResidueProduct

/-!
# Algebra of cyclotomic power-residue symbols

This file proves multiplication and `p`-th-power formulas in the numerator
of the direct power-residue symbol.  Total-symbol multiplication is stated
only away from both numerators and `p`: the total symbol is deliberately set
to one at bad primes, so an unconditional multiplication formula would be
false.  The corresponding fractional formula therefore carries explicit
support-avoidance hypotheses.
-/

open scoped NumberField nonZeroDivisors

namespace NumberTheory.CyclotomicCharacter.InverseExtension

variable {p : ℕ} [Fact p.Prime]

omit [Fact p.Prime] in
private theorem mul_not_mem_finitePrime
    (v : FinitePrime (PrimeCyclotomicField p))
    (eta xi : NumberField.RingOfIntegers (PrimeCyclotomicField p))
    (heta : eta ∉ v.asIdeal) (hxi : xi ∉ v.asIdeal) :
    eta * xi ∉ v.asIdeal := by
  simpa only [v.isPrime.mul_mem_iff_mem_or_mem, not_or] using ⟨heta, hxi⟩

omit [Fact p.Prime] in
private theorem pow_not_mem_finitePrime
    (v : FinitePrime (PrimeCyclotomicField p))
    (eta : NumberField.RingOfIntegers (PrimeCyclotomicField p))
    (n : ℕ) (hn : 0 < n) (heta : eta ∉ v.asIdeal) :
    eta ^ n ∉ v.asIdeal := by
  rwa [v.isPrime.pow_mem_iff_mem n hn]

omit [Fact p.Prime] in
private theorem residueUnitAt_mul
    (v : FinitePrime (PrimeCyclotomicField p))
    (eta xi : NumberField.RingOfIntegers (PrimeCyclotomicField p))
    (heta : eta ∉ v.asIdeal) (hxi : xi ∉ v.asIdeal) :
    residueUnitAt v (eta * xi)
        (mul_not_mem_finitePrime v eta xi heta hxi) =
      residueUnitAt v eta heta * residueUnitAt v xi hxi := by
  apply Units.ext
  exact map_mul (Ideal.Quotient.mk v.asIdeal) eta xi

omit [Fact p.Prime] in
private theorem residueUnitAt_pow
    (v : FinitePrime (PrimeCyclotomicField p))
    (eta : NumberField.RingOfIntegers (PrimeCyclotomicField p))
    (n : ℕ) (hn : 0 < n) (heta : eta ∉ v.asIdeal) :
    residueUnitAt v (eta ^ n)
        (pow_not_mem_finitePrime v eta n hn heta) =
      residueUnitAt v eta heta ^ n := by
  apply Units.ext
  exact map_pow (Ideal.Quotient.mk v.asIdeal) eta n

omit [Fact p.Prime] in
private theorem residueUnitAt_pow_absNorm_sub_one
    (v : FinitePrime (PrimeCyclotomicField p))
    (eta : NumberField.RingOfIntegers (PrimeCyclotomicField p))
    (heta : eta ∉ v.asIdeal) :
    residueUnitAt v eta heta ^ (Ideal.absNorm v.asIdeal - 1) = 1 := by
  letI := Ideal.Quotient.field v.asIdeal
  change residueUnitAt v eta heta ^
    (Nat.card
      ((NumberField.RingOfIntegers (PrimeCyclotomicField p)) ⧸
        v.asIdeal) - 1) = 1
  rw [← Nat.card_units]
  exact pow_card_eq_one' (x := residueUnitAt v eta heta)

/-- Away from both numerators and `p`, the direct prime power-residue symbol
is multiplicative in its numerator. -/
theorem pthPowerResidueSymbolAtPrime_mul
    (v : FinitePrime (PrimeCyclotomicField p))
    (eta xi : NumberField.RingOfIntegers (PrimeCyclotomicField p))
    (heta : eta ∉ v.asIdeal) (hxi : xi ∉ v.asIdeal)
    (hpv : (p : NumberField.RingOfIntegers (PrimeCyclotomicField p)) ∉
      v.asIdeal) :
    pthPowerResidueSymbolAtPrime v (eta * xi)
        (mul_not_mem_finitePrime v eta xi heta hxi) hpv =
      pthPowerResidueSymbolAtPrime v eta heta hpv *
        pthPowerResidueSymbolAtPrime v xi hxi hpv := by
  apply rootsOfUnityReductionAt_injective v hpv
  rw [rootsOfUnityReductionAt_pthPowerResidueSymbolAtPrime, map_mul,
    rootsOfUnityReductionAt_pthPowerResidueSymbolAtPrime,
    rootsOfUnityReductionAt_pthPowerResidueSymbolAtPrime]
  rw [residuePowerRootAt_coe, residuePowerRootAt_coe,
    residuePowerRootAt_coe, residueUnitAt_mul, mul_pow]

/-- Away from its numerator and `p`, the direct symbol of a `p`-th-power
numerator is one. -/
theorem pthPowerResidueSymbolAtPrime_pow_prime_eq_one
    (v : FinitePrime (PrimeCyclotomicField p))
    (eta : NumberField.RingOfIntegers (PrimeCyclotomicField p))
    (heta : eta ∉ v.asIdeal)
    (hpv : (p : NumberField.RingOfIntegers (PrimeCyclotomicField p)) ∉
      v.asIdeal) :
    pthPowerResidueSymbolAtPrime v (eta ^ p)
        (pow_not_mem_finitePrime v eta p (Fact.out : p.Prime).pos heta) hpv =
      1 := by
  apply rootsOfUnityReductionAt_injective v hpv
  rw [rootsOfUnityReductionAt_pthPowerResidueSymbolAtPrime, map_one]
  rw [residuePowerRootAt_coe,
    residueUnitAt_pow v eta p (Fact.out : p.Prime).pos heta]
  rw [← pow_mul, Nat.mul_comm,
    Nat.div_mul_cancel (prime_dvd_absNorm_sub_one v hpv)]
  exact residueUnitAt_pow_absNorm_sub_one v eta heta

/-- The total prime symbol is multiplicative in the numerator provided the
prime avoids both numerators and `p`. -/
theorem totalPthPowerResidueSymbolAtPrime_mul_of_not_mem
    (v : FinitePrime (PrimeCyclotomicField p))
    (eta xi : NumberField.RingOfIntegers (PrimeCyclotomicField p))
    (heta : eta ∉ v.asIdeal) (hxi : xi ∉ v.asIdeal)
    (hpv : (p : NumberField.RingOfIntegers (PrimeCyclotomicField p)) ∉
      v.asIdeal) :
    totalPthPowerResidueSymbolAtPrime (eta * xi) v =
      totalPthPowerResidueSymbolAtPrime eta v *
        totalPthPowerResidueSymbolAtPrime xi v := by
  rw [totalPthPowerResidueSymbolAtPrime_of_not_mem _ _
      (mul_not_mem_finitePrime v eta xi heta hxi) hpv,
    totalPthPowerResidueSymbolAtPrime_of_not_mem _ _ heta hpv,
    totalPthPowerResidueSymbolAtPrime_of_not_mem _ _ hxi hpv,
    pthPowerResidueSymbolAtPrime_mul]

/-- The total symbol of a `p`-th-power numerator is one at every finite
prime, including the primes where the direct symbol is not defined. -/
theorem totalPthPowerResidueSymbolAtPrime_pow_prime_eq_one
    (v : FinitePrime (PrimeCyclotomicField p))
    (eta : NumberField.RingOfIntegers (PrimeCyclotomicField p)) :
    totalPthPowerResidueSymbolAtPrime (eta ^ p) v = 1 := by
  by_cases heta : eta ∈ v.asIdeal
  · exact totalPthPowerResidueSymbolAtPrime_of_numerator_mem _ _
      (v.asIdeal.pow_mem_of_mem heta p (Fact.out : p.Prime).pos)
  · by_cases hpv : (p : NumberField.RingOfIntegers
        (PrimeCyclotomicField p)) ∈ v.asIdeal
    · exact totalPthPowerResidueSymbolAtPrime_of_prime_mem _ _ hpv
    · rw [totalPthPowerResidueSymbolAtPrime_of_not_mem _ _
        (pow_not_mem_finitePrime v eta p (Fact.out : p.Prime).pos heta) hpv]
      exact pthPowerResidueSymbolAtPrime_pow_prime_eq_one v eta heta hpv

/-- On a fractional ideal whose divisor support avoids both numerators and
`p`, the fractional residue product is multiplicative in the numerator. -/
theorem fractionalPthPowerResidueSymbol_mul_of_support
    (eta xi : NumberField.RingOfIntegers (PrimeCyclotomicField p))
    (I : (FractionalIdeal
      (nonZeroDivisors
        (NumberField.RingOfIntegers (PrimeCyclotomicField p)))
      (PrimeCyclotomicField p))ˣ)
    (heta : ∀ v,
      NumberTheory.UnramifiedArtin.fractionalIdealDivisor
          (NumberField.RingOfIntegers (PrimeCyclotomicField p))
          (PrimeCyclotomicField p) (Additive.ofMul I) v ≠ 0 →
        eta ∉ v.asIdeal)
    (hxi : ∀ v,
      NumberTheory.UnramifiedArtin.fractionalIdealDivisor
          (NumberField.RingOfIntegers (PrimeCyclotomicField p))
          (PrimeCyclotomicField p) (Additive.ofMul I) v ≠ 0 →
        xi ∉ v.asIdeal)
    (hp : ∀ v,
      NumberTheory.UnramifiedArtin.fractionalIdealDivisor
          (NumberField.RingOfIntegers (PrimeCyclotomicField p))
          (PrimeCyclotomicField p) (Additive.ofMul I) v ≠ 0 →
        (p : NumberField.RingOfIntegers (PrimeCyclotomicField p)) ∉
          v.asIdeal) :
    fractionalPthPowerResidueSymbol (eta * xi) I =
      fractionalPthPowerResidueSymbol eta I *
        fractionalPthPowerResidueSymbol xi I := by
  classical
  rw [fractionalPthPowerResidueSymbol_apply,
    fractionalPthPowerResidueSymbol_apply,
    fractionalPthPowerResidueSymbol_apply, ← Finsupp.prod_mul]
  apply Finsupp.prod_congr
  intro v hv
  have hv0 := Finsupp.mem_support_iff.mp hv
  rw [totalPthPowerResidueSymbolAtPrime_mul_of_not_mem v eta xi
      (heta v hv0) (hxi v hv0) (hp v hv0), mul_zpow]

/-- A `p`-th-power numerator has trivial residue product on every nonzero
fractional ideal. -/
theorem fractionalPthPowerResidueSymbol_numerator_pow_prime_eq_one
    (eta : NumberField.RingOfIntegers (PrimeCyclotomicField p))
    (I : (FractionalIdeal
      (nonZeroDivisors
        (NumberField.RingOfIntegers (PrimeCyclotomicField p)))
      (PrimeCyclotomicField p))ˣ) :
    fractionalPthPowerResidueSymbol (eta ^ p) I = 1 := by
  have hhom : fractionalPthPowerResidueSymbol (eta ^ p) = 1 := by
    apply NumberTheory.UnramifiedArtin.fractionalIdealMonoidHom_ext
    intro v
    rw [fractionalPthPowerResidueSymbol_prime,
      totalPthPowerResidueSymbolAtPrime_pow_prime_eq_one]
    rfl
  have h := DFunLike.congr_fun hhom I
  simpa using h

end NumberTheory.CyclotomicCharacter.InverseExtension
