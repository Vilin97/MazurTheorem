/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
import MazurTorsion.NumberTheory.CyclotomicKummerResidueProduct

/-!
# Galois covariance of cyclotomic power-residue symbols

This file proves that the direct `p`-th power-residue symbol is equivariant
for the natural Galois actions on its numerator and finite prime.  The same
formula is then extended to the total prime symbol and to nonzero fractional
ideals.
-/

open scoped NumberField nonZeroDivisors

namespace NumberTheory.CyclotomicCharacter.InverseExtension

variable {p : ℕ} [Fact p.Prime]

omit [Fact p.Prime] in
/-- Membership in a finite prime is preserved by simultaneous Galois
transport of the element and the prime. -/
theorem baseIntegerEquiv_mem_mapFinitePrime_iff
    (sigma : Gal(PrimeCyclotomicField p/ℚ))
    (v : FinitePrime (PrimeCyclotomicField p))
    (eta : NumberField.RingOfIntegers (PrimeCyclotomicField p)) :
    baseIntegerEquiv sigma eta ∈ (mapFinitePrime sigma v).asIdeal ↔
      eta ∈ v.asIdeal := by
  rw [mapFinitePrime_asIdeal, Ideal.apply_mem_of_equiv_iff]

omit [Fact p.Prime] in
/-- Nonmembership in a finite prime is preserved by simultaneous Galois
transport of the element and the prime. -/
theorem baseIntegerEquiv_not_mem_mapFinitePrime
    (sigma : Gal(PrimeCyclotomicField p/ℚ))
    (v : FinitePrime (PrimeCyclotomicField p))
    (eta : NumberField.RingOfIntegers (PrimeCyclotomicField p))
    (heta : eta ∉ v.asIdeal) :
    baseIntegerEquiv sigma eta ∉ (mapFinitePrime sigma v).asIdeal := by
  rwa [baseIntegerEquiv_mem_mapFinitePrime_iff]

omit [Fact p.Prime] in
/-- The rational prime remains outside a transported finite prime whenever
it was outside the original prime. -/
theorem prime_not_mem_mapFinitePrime
    (sigma : Gal(PrimeCyclotomicField p/ℚ))
    (v : FinitePrime (PrimeCyclotomicField p))
    (hpv : (p : NumberField.RingOfIntegers (PrimeCyclotomicField p)) ∉
      v.asIdeal) :
    (p : NumberField.RingOfIntegers (PrimeCyclotomicField p)) ∉
      (mapFinitePrime sigma v).asIdeal := by
  have h := baseIntegerEquiv_not_mem_mapFinitePrime sigma v
    (p : NumberField.RingOfIntegers (PrimeCyclotomicField p)) hpv
  simpa using h

private noncomputable def residueQuotientEquiv
    (sigma : Gal(PrimeCyclotomicField p/ℚ))
    (v : FinitePrime (PrimeCyclotomicField p)) :
    (NumberField.RingOfIntegers (PrimeCyclotomicField p) ⧸ v.asIdeal) ≃+*
      (NumberField.RingOfIntegers (PrimeCyclotomicField p) ⧸
        (mapFinitePrime sigma v).asIdeal) :=
  Ideal.quotientEquiv v.asIdeal (mapFinitePrime sigma v).asIdeal
    (baseIntegerEquiv sigma) (mapFinitePrime_asIdeal sigma v)

omit [Fact p.Prime] in
private theorem absNorm_mapFinitePrime
    (sigma : Gal(PrimeCyclotomicField p/ℚ))
    (v : FinitePrime (PrimeCyclotomicField p)) :
    Ideal.absNorm (mapFinitePrime sigma v).asIdeal =
      Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply,
    Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr (residueQuotientEquiv sigma v).symm.toEquiv

omit [Fact p.Prime] in
private theorem residueQuotientEquiv_residueUnitAt
    (sigma : Gal(PrimeCyclotomicField p/ℚ))
    (v : FinitePrime (PrimeCyclotomicField p))
    (eta : NumberField.RingOfIntegers (PrimeCyclotomicField p))
    (heta : eta ∉ v.asIdeal) :
    Units.mapEquiv (residueQuotientEquiv sigma v).toMulEquiv
        (residueUnitAt v eta heta) =
      residueUnitAt (mapFinitePrime sigma v) (baseIntegerEquiv sigma eta)
        (baseIntegerEquiv_not_mem_mapFinitePrime sigma v eta heta) := by
  apply Units.ext
  exact Ideal.quotientEquiv_mk v.asIdeal
    (mapFinitePrime sigma v).asIdeal (baseIntegerEquiv sigma)
    (mapFinitePrime_asIdeal sigma v) eta

private theorem residueQuotientEquiv_residuePowerRootAt
    (sigma : Gal(PrimeCyclotomicField p/ℚ))
    (v : FinitePrime (PrimeCyclotomicField p))
    (eta : NumberField.RingOfIntegers (PrimeCyclotomicField p))
    (heta : eta ∉ v.asIdeal)
    (hpv : (p : NumberField.RingOfIntegers (PrimeCyclotomicField p)) ∉
      v.asIdeal) :
    Units.mapEquiv (residueQuotientEquiv sigma v).toMulEquiv
        (residuePowerRootAt v eta heta hpv :
          ((NumberField.RingOfIntegers (PrimeCyclotomicField p) ⧸
            v.asIdeal)ˣ)) =
      (residuePowerRootAt (mapFinitePrime sigma v)
        (baseIntegerEquiv sigma eta)
        (baseIntegerEquiv_not_mem_mapFinitePrime sigma v eta heta)
        (prime_not_mem_mapFinitePrime sigma v hpv) :
          ((NumberField.RingOfIntegers (PrimeCyclotomicField p) ⧸
            (mapFinitePrime sigma v).asIdeal)ˣ)) := by
  rw [residuePowerRootAt_coe, residuePowerRootAt_coe,
    map_pow, residueQuotientEquiv_residueUnitAt,
    absNorm_mapFinitePrime]

private theorem map_rootsOfUnity_eq_pow_directCharacter
    (sigma : Gal(PrimeCyclotomicField p/ℚ))
    (zeta : rootsOfUnity p (PrimeCyclotomicField p)) :
    sigma.toRingEquiv.restrictRootsOfUnity p zeta =
      zeta ^ (((directCharacter p sigma : (ZMod p)ˣ) : ZMod p).val) := by
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  letI : NeZero (p : ℚ) :=
    ⟨Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero⟩
  letI : IsCyclotomicExtension {p} ℚ (PrimeCyclotomicField p) :=
    CyclotomicField.isCyclotomicExtension p ℚ
  have hchar : directCharacter p sigma =
      IsCyclotomicExtension.Rat.galEquivZMod p
        (PrimeCyclotomicField p) sigma := by
    change ((IsCyclotomicExtension.autEquivPow
      (PrimeCyclotomicField p) _ sigma)⁻¹)⁻¹ = _
    rw [inv_inv]
  apply Subtype.ext
  apply Units.ext
  have hzeta : (((zeta : (PrimeCyclotomicField p)ˣ) :
      PrimeCyclotomicField p) ^ p) = 1 := by
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using
      congrArg Units.val zeta.property
  change sigma (((zeta : (PrimeCyclotomicField p)ˣ) :
      PrimeCyclotomicField p)) =
    (((zeta ^ (((directCharacter p sigma : (ZMod p)ˣ) : ZMod p).val) :
      rootsOfUnity p (PrimeCyclotomicField p)) :
        (PrimeCyclotomicField p)ˣ) : PrimeCyclotomicField p)
  simpa only [rootsOfUnity.coe_pow, Units.val_pow_eq_pow_val, hchar] using
    IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq
      p (PrimeCyclotomicField p) sigma hzeta

private theorem integralRootsOfUnityEquiv_symm_coe
    (zeta : rootsOfUnity p (PrimeCyclotomicField p)) :
    (algebraMap
      (NumberField.RingOfIntegers (PrimeCyclotomicField p))
      (PrimeCyclotomicField p))
        (↑(↑((integralRootsOfUnityEquiv p).symm zeta) :
          (NumberField.RingOfIntegers (PrimeCyclotomicField p))ˣ) :
            NumberField.RingOfIntegers (PrimeCyclotomicField p)) =
      ((zeta : (PrimeCyclotomicField p)ˣ) : PrimeCyclotomicField p) := by
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  simpa only [integralRootsOfUnityEquiv] using
    (rootsOfUnityEquivOfPrimitiveRoots_symm_apply
      NumberField.RingOfIntegers.coe_injective
      ⟨(primeCyclotomicZeta_spec p).toInteger,
        (mem_primitiveRoots (Fact.out : p.Prime).pos).mpr
          (primeCyclotomicZeta_spec p).toInteger_isPrimitiveRoot⟩ zeta)

private theorem baseIntegerEquiv_integralRootsOfUnityEquiv_symm
    (sigma : Gal(PrimeCyclotomicField p/ℚ))
    (zeta : rootsOfUnity p (PrimeCyclotomicField p)) :
    baseIntegerEquiv sigma
        (((integralRootsOfUnityEquiv p).symm zeta :
          rootsOfUnity p
            (NumberField.RingOfIntegers (PrimeCyclotomicField p))) :
              (NumberField.RingOfIntegers (PrimeCyclotomicField p))ˣ) =
      (((integralRootsOfUnityEquiv p).symm
          (sigma.toRingEquiv.restrictRootsOfUnity p zeta) :
        rootsOfUnity p
          (NumberField.RingOfIntegers (PrimeCyclotomicField p))) :
            (NumberField.RingOfIntegers (PrimeCyclotomicField p))ˣ) := by
  apply NumberField.RingOfIntegers.ext
  have hzeta := integralRootsOfUnityEquiv_symm_coe zeta
  have hsigma := integralRootsOfUnityEquiv_symm_coe
    (sigma.toRingEquiv.restrictRootsOfUnity p zeta)
  change
    (↑(↑(↑((integralRootsOfUnityEquiv p).symm zeta) :
      (NumberField.RingOfIntegers (PrimeCyclotomicField p))ˣ) :
        NumberField.RingOfIntegers (PrimeCyclotomicField p)) :
          PrimeCyclotomicField p) =
      ((zeta : (PrimeCyclotomicField p)ˣ) : PrimeCyclotomicField p) at hzeta
  change
    (↑(↑(↑((integralRootsOfUnityEquiv p).symm
      (sigma.toRingEquiv.restrictRootsOfUnity p zeta)) :
        (NumberField.RingOfIntegers (PrimeCyclotomicField p))ˣ) :
          NumberField.RingOfIntegers (PrimeCyclotomicField p)) :
            PrimeCyclotomicField p) =
      (((sigma.toRingEquiv.restrictRootsOfUnity p zeta :
        rootsOfUnity p (PrimeCyclotomicField p)) :
          (PrimeCyclotomicField p)ˣ) : PrimeCyclotomicField p) at hsigma
  change
    sigma
        (((((integralRootsOfUnityEquiv p).symm zeta :
          rootsOfUnity p
            (NumberField.RingOfIntegers (PrimeCyclotomicField p))) :
              (NumberField.RingOfIntegers (PrimeCyclotomicField p))ˣ) :
                NumberField.RingOfIntegers (PrimeCyclotomicField p)) :
                  PrimeCyclotomicField p) =
      (((((integralRootsOfUnityEquiv p).symm
          (sigma.toRingEquiv.restrictRootsOfUnity p zeta) :
            rootsOfUnity p
              (NumberField.RingOfIntegers (PrimeCyclotomicField p))) :
                (NumberField.RingOfIntegers (PrimeCyclotomicField p))ˣ) :
                  NumberField.RingOfIntegers (PrimeCyclotomicField p)) :
                    PrimeCyclotomicField p)
  rw [hzeta, hsigma]
  rfl

private theorem residueQuotientEquiv_rootsOfUnityReductionAt
    (sigma : Gal(PrimeCyclotomicField p/ℚ))
    (v : FinitePrime (PrimeCyclotomicField p))
    (zeta : rootsOfUnity p (PrimeCyclotomicField p)) :
    Units.mapEquiv (residueQuotientEquiv sigma v).toMulEquiv
        (rootsOfUnityReductionAt v zeta) =
      rootsOfUnityReductionAt (mapFinitePrime sigma v)
        (sigma.toRingEquiv.restrictRootsOfUnity p zeta) := by
  apply Units.ext
  change
    residueQuotientEquiv sigma v
        (Ideal.Quotient.mk v.asIdeal
          (↑(↑((integralRootsOfUnityEquiv p).symm zeta) :
            (NumberField.RingOfIntegers (PrimeCyclotomicField p))ˣ) :
              NumberField.RingOfIntegers (PrimeCyclotomicField p))) =
      Ideal.Quotient.mk (mapFinitePrime sigma v).asIdeal
        (↑(↑((integralRootsOfUnityEquiv p).symm
          (sigma.toRingEquiv.restrictRootsOfUnity p zeta)) :
            (NumberField.RingOfIntegers (PrimeCyclotomicField p))ˣ) :
              NumberField.RingOfIntegers (PrimeCyclotomicField p))
  change
    Ideal.Quotient.mk (mapFinitePrime sigma v).asIdeal
        (baseIntegerEquiv sigma
          (↑(↑((integralRootsOfUnityEquiv p).symm zeta) :
            (NumberField.RingOfIntegers (PrimeCyclotomicField p))ˣ) :
              NumberField.RingOfIntegers (PrimeCyclotomicField p))) =
      Ideal.Quotient.mk (mapFinitePrime sigma v).asIdeal
        (↑(↑((integralRootsOfUnityEquiv p).symm
          (sigma.toRingEquiv.restrictRootsOfUnity p zeta)) :
            (NumberField.RingOfIntegers (PrimeCyclotomicField p))ˣ) :
              NumberField.RingOfIntegers (PrimeCyclotomicField p))
  exact congrArg (Ideal.Quotient.mk (mapFinitePrime sigma v).asIdeal)
    (baseIntegerEquiv_integralRootsOfUnityEquiv_symm sigma zeta)

/-- The direct prime `p`-th power-residue symbol is Galois covariant when
both its numerator and finite prime are transported. -/
theorem pthPowerResidueSymbolAtPrime_mapFinitePrime
    (sigma : Gal(PrimeCyclotomicField p/ℚ))
    (v : FinitePrime (PrimeCyclotomicField p))
    (eta : NumberField.RingOfIntegers (PrimeCyclotomicField p))
    (heta : eta ∉ v.asIdeal)
    (hpv : (p : NumberField.RingOfIntegers (PrimeCyclotomicField p)) ∉
      v.asIdeal) :
    pthPowerResidueSymbolAtPrime (mapFinitePrime sigma v)
        (baseIntegerEquiv sigma eta)
        (baseIntegerEquiv_not_mem_mapFinitePrime sigma v eta heta)
        (prime_not_mem_mapFinitePrime sigma v hpv) =
      (pthPowerResidueSymbolAtPrime v eta heta hpv) ^
        (((directCharacter p sigma : (ZMod p)ˣ) : ZMod p).val) := by
  apply rootsOfUnityReductionAt_injective (mapFinitePrime sigma v)
    (prime_not_mem_mapFinitePrime sigma v hpv)
  let zeta := pthPowerResidueSymbolAtPrime v eta heta hpv
  calc
    rootsOfUnityReductionAt (mapFinitePrime sigma v)
        (pthPowerResidueSymbolAtPrime (mapFinitePrime sigma v)
          (baseIntegerEquiv sigma eta)
          (baseIntegerEquiv_not_mem_mapFinitePrime sigma v eta heta)
          (prime_not_mem_mapFinitePrime sigma v hpv)) =
        (residuePowerRootAt (mapFinitePrime sigma v)
          (baseIntegerEquiv sigma eta)
          (baseIntegerEquiv_not_mem_mapFinitePrime sigma v eta heta)
          (prime_not_mem_mapFinitePrime sigma v hpv) :
            ((NumberField.RingOfIntegers (PrimeCyclotomicField p) ⧸
              (mapFinitePrime sigma v).asIdeal)ˣ)) :=
      rootsOfUnityReductionAt_pthPowerResidueSymbolAtPrime _ _ _ _
    _ = Units.mapEquiv (residueQuotientEquiv sigma v).toMulEquiv
        (residuePowerRootAt v eta heta hpv :
          ((NumberField.RingOfIntegers (PrimeCyclotomicField p) ⧸
            v.asIdeal)ˣ)) :=
      (residueQuotientEquiv_residuePowerRootAt sigma v eta heta hpv).symm
    _ = Units.mapEquiv (residueQuotientEquiv sigma v).toMulEquiv
        (rootsOfUnityReductionAt v zeta) := by
      rw [rootsOfUnityReductionAt_pthPowerResidueSymbolAtPrime]
    _ = rootsOfUnityReductionAt (mapFinitePrime sigma v)
        (sigma.toRingEquiv.restrictRootsOfUnity p zeta) :=
      residueQuotientEquiv_rootsOfUnityReductionAt sigma v zeta
    _ = rootsOfUnityReductionAt (mapFinitePrime sigma v)
        (zeta ^ (((directCharacter p sigma : (ZMod p)ˣ) : ZMod p).val)) := by
      rw [map_rootsOfUnity_eq_pow_directCharacter]

/-- The total prime `p`-th power-residue symbol is Galois covariant.  At
primes dividing the numerator or `p`, both sides are one. -/
theorem totalPthPowerResidueSymbolAtPrime_mapFinitePrime
    (sigma : Gal(PrimeCyclotomicField p/ℚ))
    (v : FinitePrime (PrimeCyclotomicField p))
    (eta : NumberField.RingOfIntegers (PrimeCyclotomicField p)) :
    totalPthPowerResidueSymbolAtPrime (baseIntegerEquiv sigma eta)
        (mapFinitePrime sigma v) =
      (totalPthPowerResidueSymbolAtPrime eta v) ^
        (((directCharacter p sigma : (ZMod p)ˣ) : ZMod p).val) := by
  classical
  by_cases heta : eta ∈ v.asIdeal
  · have hmap : baseIntegerEquiv sigma eta ∈
        (mapFinitePrime sigma v).asIdeal :=
      (baseIntegerEquiv_mem_mapFinitePrime_iff sigma v eta).2 heta
    rw [totalPthPowerResidueSymbolAtPrime_of_numerator_mem _ _ hmap,
      totalPthPowerResidueSymbolAtPrime_of_numerator_mem _ _ heta, one_pow]
  · have hmap : baseIntegerEquiv sigma eta ∉
        (mapFinitePrime sigma v).asIdeal :=
      baseIntegerEquiv_not_mem_mapFinitePrime sigma v eta heta
    by_cases hpv : (p : NumberField.RingOfIntegers
        (PrimeCyclotomicField p)) ∈ v.asIdeal
    · have hpmap : (p : NumberField.RingOfIntegers
          (PrimeCyclotomicField p)) ∈ (mapFinitePrime sigma v).asIdeal := by
        have h := (baseIntegerEquiv_mem_mapFinitePrime_iff sigma v
          (p : NumberField.RingOfIntegers (PrimeCyclotomicField p))).2 hpv
        simpa using h
      rw [totalPthPowerResidueSymbolAtPrime_of_prime_mem _ _ hpmap,
        totalPthPowerResidueSymbolAtPrime_of_prime_mem _ _ hpv, one_pow]
    · have hpmap := prime_not_mem_mapFinitePrime sigma v hpv
      rw [totalPthPowerResidueSymbolAtPrime_of_not_mem _ _ hmap hpmap,
        totalPthPowerResidueSymbolAtPrime_of_not_mem _ _ heta hpv,
        pthPowerResidueSymbolAtPrime_mapFinitePrime]

/-- The fractional `p`-th power-residue symbol is Galois covariant under
simultaneous transport of its integral numerator and fractional ideal. -/
theorem fractionalPthPowerResidueSymbol_map
    (sigma : Gal(PrimeCyclotomicField p/ℚ))
    (eta : NumberField.RingOfIntegers (PrimeCyclotomicField p))
    (I : (FractionalIdeal
      (nonZeroDivisors
        (NumberField.RingOfIntegers (PrimeCyclotomicField p)))
      (PrimeCyclotomicField p))ˣ) :
    fractionalPthPowerResidueSymbol (baseIntegerEquiv sigma eta)
        (fractionalIdealEquiv sigma I) =
      (fractionalPthPowerResidueSymbol eta I) ^
        (((directCharacter p sigma : (ZMod p)ˣ) : ZMod p).val) := by
  let exponent := (((directCharacter p sigma : (ZMod p)ˣ) : ZMod p).val)
  have hhom :
      (fractionalPthPowerResidueSymbol (baseIntegerEquiv sigma eta)).comp
          (fractionalIdealEquiv sigma).toMonoidHom =
        (fractionalPthPowerResidueSymbol eta) ^ exponent := by
    apply NumberTheory.UnramifiedArtin.fractionalIdealMonoidHom_ext
    intro v
    change
      fractionalPthPowerResidueSymbol (baseIntegerEquiv sigma eta)
          (fractionalIdealEquiv sigma
            (NumberTheory.UnramifiedArtin.primeFractionalIdealUnit
              (K := PrimeCyclotomicField p) v)) =
        (fractionalPthPowerResidueSymbol eta
          (NumberTheory.UnramifiedArtin.primeFractionalIdealUnit
            (K := PrimeCyclotomicField p) v)) ^ exponent
    rw [fractionalIdealEquiv_prime,
      fractionalPthPowerResidueSymbol_prime,
      fractionalPthPowerResidueSymbol_prime,
      totalPthPowerResidueSymbolAtPrime_mapFinitePrime]
  exact DFunLike.congr_fun hhom I

end NumberTheory.CyclotomicCharacter.InverseExtension
