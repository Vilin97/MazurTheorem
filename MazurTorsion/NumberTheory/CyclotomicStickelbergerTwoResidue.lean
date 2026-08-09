/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.CyclotomicStickelbergerTwo
import MazurTorsion.NumberTheory.CyclotomicKummerResidueCovariance
import MazurTorsion.NumberTheory.CyclotomicKummerResidueAlgebra

/-!
# The corrected Stickelberger-two residue product

This file is the algebraic consumer of the corrected `b = 2` coefficients.
For one finite prime `v` of `ℚ(ζ_p)`, it forms the nonzero fractional ideal

`∏ a, σₐ⁻¹(v) ^ stickelbergerTwoCoefficient p a`.

The Kummer class of the intended numerator has direct-character weight two.
Combining that weight with Galois covariance of the residue symbol predicts

`(η / σ(v)) = (η / v) ^ directCharacter(σ)⁻¹`.

Field-valued witnesses for the equality of Kummer classes can carry
denominators.  Accordingly, `HasDirectCharacterSquareResidueWeightAt` records
exactly this symbol-level consequence, without asserting a reciprocity law or
a Jacobi-sum factorization.  A later Jacobi module is the named downstream
producer of this interface; `jacobiStickelbergerTwoResidueConsumer` is its
checked consumer.
-/

open scoped BigOperators NumberField nonZeroDivisors

namespace NumberTheory.CyclotomicCharacter.InverseExtension

variable {p : ℕ} [Fact p.Prime]

local notation "OK" =>
  NumberField.RingOfIntegers (PrimeCyclotomicField p)

local notation "FI" =>
  (FractionalIdeal (nonZeroDivisors OK) (PrimeCyclotomicField p))ˣ

/-- The direct cyclotomic character, packaged as the standard equivalence.
This is used only to choose the automorphism with prescribed character. -/
noncomputable def directCharacterEquiv (p : ℕ) [Fact p.Prime] :
    Gal(PrimeCyclotomicField p/ℚ) ≃* (ZMod p)ˣ :=
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  letI : NeZero (p : ℚ) :=
    ⟨Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero⟩
  letI : IsCyclotomicExtension {p} ℚ (PrimeCyclotomicField p) :=
    CyclotomicField.isCyclotomicExtension p ℚ
  IsCyclotomicExtension.autEquivPow
    (PrimeCyclotomicField p)
    (Polynomial.cyclotomic.irreducible_rat (Fact.out : p.Prime).pos)

@[simp]
theorem directCharacterEquiv_apply
    (sigma : Gal(PrimeCyclotomicField p/ℚ)) :
    directCharacterEquiv p sigma = directCharacter p sigma := by
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  letI : NeZero (p : ℚ) :=
    ⟨Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero⟩
  letI : IsCyclotomicExtension {p} ℚ (PrimeCyclotomicField p) :=
    CyclotomicField.isCyclotomicExtension p ℚ
  change (IsCyclotomicExtension.autEquivPow
    (PrimeCyclotomicField p) _ sigma) =
      ((IsCyclotomicExtension.autEquivPow
        (PrimeCyclotomicField p) _ sigma)⁻¹)⁻¹
  rw [inv_inv]

/-- The automorphism whose direct cyclotomic character is `a`. -/
noncomputable def galoisOfDirectCharacter (a : (ZMod p)ˣ) :
    Gal(PrimeCyclotomicField p/ℚ) :=
  (directCharacterEquiv p).symm a

@[simp]
theorem directCharacter_galoisOfDirectCharacter (a : (ZMod p)ˣ) :
    directCharacter p (galoisOfDirectCharacter a) = a := by
  rw [← directCharacterEquiv_apply]
  exact (directCharacterEquiv p).apply_symm_apply a

/-- The corrected `b = 2` product of the Galois conjugates of one finite
prime.  The inverse in `galoisOfDirectCharacter a⁻¹` matches the coefficient
of `σₐ⁻¹` in the corrected Stickelberger element. -/
noncomputable def stickelbergerTwoPrimeIdeal
    (v : FinitePrime (PrimeCyclotomicField p)) : FI :=
  ∏ a : (ZMod p)ˣ,
    (NumberTheory.UnramifiedArtin.primeFractionalIdealUnit
      (K := PrimeCyclotomicField p)
      (mapFinitePrime (galoisOfDirectCharacter a⁻¹) v)) ^
        stickelbergerTwoCoefficient p a

/-- The corresponding product of total prime residue symbols. -/
noncomputable def stickelbergerTwoResidueProduct
    (eta : OK) (v : FinitePrime (PrimeCyclotomicField p)) :
    rootsOfUnity p (PrimeCyclotomicField p) :=
  ∏ a : (ZMod p)ˣ,
    (totalPthPowerResidueSymbolAtPrime eta
      (mapFinitePrime (galoisOfDirectCharacter a⁻¹) v)) ^
        stickelbergerTwoCoefficient p a

/-- Evaluation of the fractional residue symbol on the corrected ideal is
definitionally the corrected product of total prime symbols. -/
theorem fractionalPthPowerResidueSymbol_stickelbergerTwoPrimeIdeal
    (eta : OK) (v : FinitePrime (PrimeCyclotomicField p)) :
    fractionalPthPowerResidueSymbol eta (stickelbergerTwoPrimeIdeal v) =
      stickelbergerTwoResidueProduct eta v := by
  simp [stickelbergerTwoPrimeIdeal, stickelbergerTwoResidueProduct,
    fractionalPthPowerResidueSymbol_prime]

/-- The exact symbol-level consequence of direct-character-square Kummer
covariance at `v`.

For an integral Kummer representative, this is what simultaneous Galois
covariance and an equality `σ(η) = η ^ directCharacter(σ)^2 * b^p` give after
all denominators have been cleared away from the relevant primes.  Keeping
that arithmetic clearance explicit prevents this algebraic module from
assuming either reciprocity or a Jacobi factorization. -/
def HasDirectCharacterSquareResidueWeightAt
    (eta : OK) (v : FinitePrime (PrimeCyclotomicField p)) : Prop :=
  ∀ sigma : Gal(PrimeCyclotomicField p/ℚ),
    totalPthPowerResidueSymbolAtPrime eta (mapFinitePrime sigma v) =
      (totalPthPowerResidueSymbolAtPrime eta v) ^
        (((directCharacter p sigma)⁻¹ : (ZMod p)ˣ) : ZMod p).val

omit [Fact p.Prime] in
private theorem rootsOfUnity_pow_prime_eq_one
    (x : rootsOfUnity p (PrimeCyclotomicField p)) : x ^ p = 1 := by
  apply Subtype.ext
  exact x.property

private theorem totalPthPowerResidueSymbolAtPrime_pow_succ_of_not_mem
    (v : FinitePrime (PrimeCyclotomicField p)) (eta : OK) (n : ℕ)
    (heta : eta ∉ v.asIdeal)
    (hpv : (p : OK) ∉ v.asIdeal) :
    totalPthPowerResidueSymbolAtPrime (eta ^ (n + 1)) v =
      (totalPthPowerResidueSymbolAtPrime eta v) ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hpow : eta ^ (n + 1) ∉ v.asIdeal := by
        intro hmem
        exact heta ((v.isPrime.pow_mem_iff_mem (n + 1) (by omega)).mp hmem)
      rw [show eta ^ (n + 1 + 1) = eta ^ (n + 1) * eta by rw [pow_succ]]
      rw [totalPthPowerResidueSymbolAtPrime_mul_of_not_mem
        v (eta ^ (n + 1)) eta hpow heta hpv, ih]
      exact (pow_succ _ (n + 1)).symm

/-- Integral-witness producer for the symbol-level square-weight interface.

The only support hypotheses are that the base prime avoids `eta` and `p`.
For every cyclotomic automorphism, the witness `b` is integral and satisfies

`σ(eta) = eta ^ directCharacter(σ)^2 * b^p`.

The equality itself forces both `eta` and `b` to avoid `σ(v)`, so no redundant
orbitwise nonmembership hypotheses are required. -/
theorem HasDirectCharacterSquareResidueWeightAt.of_integral_pthPower_witnesses
    (eta : OK) (v : FinitePrime (PrimeCyclotomicField p))
    (heta : eta ∉ v.asIdeal)
    (hpv : (p : OK) ∉ v.asIdeal)
    (hwitness : ∀ sigma : Gal(PrimeCyclotomicField p/ℚ), ∃ b : OK,
      baseIntegerEquiv sigma eta =
        eta ^ (((directCharacter p sigma) ^ 2 : (ZMod p)ˣ) : ZMod p).val *
          b ^ p) :
    HasDirectCharacterSquareResidueWeightAt eta v := by
  intro sigma
  obtain ⟨b, hb⟩ := hwitness sigma
  let a : (ZMod p)ˣ := directCharacter p sigma
  let n : ℕ := ((a ^ 2 : (ZMod p)ˣ) : ZMod p).val
  let r : ℕ := (((a ^ 2 : (ZMod p)ˣ)⁻¹ : (ZMod p)ˣ) : ZMod p).val
  let m : ℕ := (a : ZMod p).val
  let t : ℕ := ((a⁻¹ : (ZMod p)ˣ) : ZMod p).val
  have hn_pos : 0 < n := by
    exact ZMod.val_pos.mpr (Units.ne_zero (a ^ 2))
  have hleft : baseIntegerEquiv sigma eta ∉
      (mapFinitePrime sigma v).asIdeal :=
    baseIntegerEquiv_not_mem_mapFinitePrime sigma v eta heta
  have heta_map : eta ∉ (mapFinitePrime sigma v).asIdeal := by
    intro hmem
    have hpow : eta ^ n ∈ (mapFinitePrime sigma v).asIdeal :=
      (mapFinitePrime sigma v).asIdeal.pow_mem_of_mem hmem n hn_pos
    apply hleft
    rw [hb]
    exact (mapFinitePrime sigma v).asIdeal.mul_mem_right (b ^ p) hpow
  have hb_map : b ∉ (mapFinitePrime sigma v).asIdeal := by
    intro hmem
    have hpow : b ^ p ∈ (mapFinitePrime sigma v).asIdeal :=
      (mapFinitePrime sigma v).asIdeal.pow_mem_of_mem hmem p
        (Fact.out : p.Prime).pos
    apply hleft
    rw [hb]
    exact (mapFinitePrime sigma v).asIdeal.mul_mem_left (eta ^ n) hpow
  have heta_pow_map : eta ^ n ∉ (mapFinitePrime sigma v).asIdeal := by
    intro hmem
    exact heta_map
      (((mapFinitePrime sigma v).isPrime.pow_mem_iff_mem n hn_pos).mp hmem)
  have hb_pow_map : b ^ p ∉ (mapFinitePrime sigma v).asIdeal := by
    intro hmem
    exact hb_map
      (((mapFinitePrime sigma v).isPrime.pow_mem_iff_mem p
        (Fact.out : p.Prime).pos).mp hmem)
  have hp_map : (p : OK) ∉ (mapFinitePrime sigma v).asIdeal :=
    prime_not_mem_mapFinitePrime sigma v hpv
  let x := totalPthPowerResidueSymbolAtPrime eta v
  let y := totalPthPowerResidueSymbolAtPrime eta (mapFinitePrime sigma v)
  have hcov := totalPthPowerResidueSymbolAtPrime_mapFinitePrime sigma v eta
  have hn_succ : ∃ k, n = k + 1 := Nat.exists_eq_succ_of_ne_zero hn_pos.ne'
  obtain ⟨k, hk⟩ := hn_succ
  have hpow_eta : totalPthPowerResidueSymbolAtPrime (eta ^ n)
      (mapFinitePrime sigma v) = y ^ n := by
    rw [hk]
    exact totalPthPowerResidueSymbolAtPrime_pow_succ_of_not_mem
      (mapFinitePrime sigma v) eta k heta_map hp_map
  have hclass : y ^ n = x ^ m := by
    rw [hb] at hcov
    rw [totalPthPowerResidueSymbolAtPrime_mul_of_not_mem
      (mapFinitePrime sigma v) (eta ^ n) (b ^ p)
      heta_pow_map hb_pow_map hp_map,
      hpow_eta,
      totalPthPowerResidueSymbolAtPrime_pow_prime_eq_one, mul_one] at hcov
    simpa only [a, m, x, y] using hcov
  have hraised : y ^ (n * r) = x ^ (m * r) := by
    calc
      y ^ (n * r) = (y ^ n) ^ r := pow_mul y n r
      _ = (x ^ m) ^ r := congrArg (fun z => z ^ r) hclass
      _ = x ^ (m * r) := (pow_mul x m r).symm
  have hn_mod : n * r ≡ 1 [MOD p] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    simp only [n, r, Nat.cast_mul, ZMod.natCast_zmod_val, Nat.cast_one]
    rw [← Units.val_mul]
    simp
  have hm_mod : m * r ≡ t [MOD p] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    simp only [m, r, t, Nat.cast_mul, ZMod.natCast_zmod_val]
    change (a : ZMod p) * ((a ^ 2)⁻¹ : (ZMod p)ˣ) = (a⁻¹ : (ZMod p)ˣ)
    rw [← Units.val_mul]
    congr 1
    group
  have hy_prime : y ^ p = 1 := rootsOfUnity_pow_prime_eq_one y
  have hx_prime : x ^ p = 1 := rootsOfUnity_pow_prime_eq_one x
  calc
    y = y ^ (n * r) := by
      rw [pow_eq_pow_of_modEq hn_mod hy_prime, pow_one]
    _ = x ^ (m * r) := hraised
    _ = x ^ t := pow_eq_pow_of_modEq hm_mod hx_prime

/-- The weight-two interface at the inverse-character representative indexed
by `a` has exponent `a`. -/
theorem HasDirectCharacterSquareResidueWeightAt.at_inverse
    {eta : OK} {v : FinitePrime (PrimeCyclotomicField p)}
    (hweight : HasDirectCharacterSquareResidueWeightAt eta v)
    (a : (ZMod p)ˣ) :
    totalPthPowerResidueSymbolAtPrime eta
        (mapFinitePrime (galoisOfDirectCharacter a⁻¹) v) =
      (totalPthPowerResidueSymbolAtPrime eta v) ^ (a : ZMod p).val := by
  rw [hweight, directCharacter_galoisOfDirectCharacter, inv_inv]

private theorem stickelbergerTwoNaturalExponent_modEq
    (p : ℕ) [Fact p.Prime] :
    (∑ a : (ZMod p)ˣ,
        (a : ZMod p).val * stickelbergerTwoCoefficient p a) ≡
      (stickelbergerTwoWeightedScalar p).val [MOD p] := by
  rw [← ZMod.natCast_eq_natCast_iff]
  simp only [stickelbergerTwoWeightedScalar, Nat.cast_sum, Nat.cast_mul,
    ZMod.natCast_zmod_val]
  apply Finset.sum_congr rfl
  intro a _
  rw [mul_comm]

/-- The corrected residue product acts through the elementary
Stickelberger-two weighted scalar. -/
theorem stickelbergerTwoResidueProduct_eq_weightedScalar
    {eta : OK} {v : FinitePrime (PrimeCyclotomicField p)}
    (hweight : HasDirectCharacterSquareResidueWeightAt eta v) :
    stickelbergerTwoResidueProduct eta v =
      (totalPthPowerResidueSymbolAtPrime eta v) ^
        (stickelbergerTwoWeightedScalar p).val := by
  let x := totalPthPowerResidueSymbolAtPrime eta v
  have hx : x ^ p = 1 := by
    apply Subtype.ext
    exact x.property
  have hmod :
      (∑ a : (ZMod p)ˣ,
          (a : ZMod p).val * stickelbergerTwoCoefficient p a) ≡
        (stickelbergerTwoWeightedScalar p).val [MOD p] := by
    exact stickelbergerTwoNaturalExponent_modEq p
  calc
    stickelbergerTwoResidueProduct eta v =
        ∏ a : (ZMod p)ˣ,
          x ^ ((a : ZMod p).val * stickelbergerTwoCoefficient p a) := by
      unfold stickelbergerTwoResidueProduct
      apply Finset.prod_congr rfl
      intro a _
      rw [hweight.at_inverse a, pow_mul]
    _ = x ^ (∑ a : (ZMod p)ˣ,
          (a : ZMod p).val * stickelbergerTwoCoefficient p a) :=
      Finset.prod_pow_eq_pow_sum Finset.univ _ _
    _ = x ^ (stickelbergerTwoWeightedScalar p).val :=
      pow_eq_pow_of_modEq hmod hx

/-- Fractional-ideal form of the corrected weighted-scalar identity. -/
theorem fractionalPthPowerResidueSymbol_stickelbergerTwoPrimeIdeal_eq_weightedScalar
    {eta : OK} {v : FinitePrime (PrimeCyclotomicField p)}
    (hweight : HasDirectCharacterSquareResidueWeightAt eta v) :
    fractionalPthPowerResidueSymbol eta (stickelbergerTwoPrimeIdeal v) =
      (totalPthPowerResidueSymbolAtPrime eta v) ^
        (stickelbergerTwoWeightedScalar p).val := by
  rw [fractionalPthPowerResidueSymbol_stickelbergerTwoPrimeIdeal]
  exact stickelbergerTwoResidueProduct_eq_weightedScalar hweight

private theorem eq_one_of_pow_weightedScalar_eq_one
    (hp5 : 5 ≤ p) (x : rootsOfUnity p (PrimeCyclotomicField p))
    (hx : x ^ (stickelbergerTwoWeightedScalar p).val = 1) :
    x = 1 := by
  have hunit : IsUnit (stickelbergerTwoWeightedScalar p) :=
    isUnit_stickelbergerTwoWeightedScalar hp5
  have hunitVal : IsUnit
      ((stickelbergerTwoWeightedScalar p).val : ZMod p) := by
    simpa only [ZMod.natCast_zmod_val] using hunit
  have hcop : (stickelbergerTwoWeightedScalar p).val.Coprime p :=
    (ZMod.isUnit_iff_coprime _ _).mp hunitVal
  have hxp : x ^ p = 1 := by
    apply Subtype.ext
    exact x.property
  exact (pow_eq_one_iff_of_coprime hcop).mp ⟨hx, hxp⟩

/-- A vanishing corrected residue product forces vanishing at its base prime
for every prime `p ≥ 5`. -/
theorem totalPthPowerResidueSymbolAtPrime_eq_one_of_stickelbergerTwoResidueProduct_eq_one
    (hp5 : 5 ≤ p) {eta : OK} {v : FinitePrime (PrimeCyclotomicField p)}
    (hweight : HasDirectCharacterSquareResidueWeightAt eta v)
    (hzero : stickelbergerTwoResidueProduct eta v = 1) :
    totalPthPowerResidueSymbolAtPrime eta v = 1 := by
  apply eq_one_of_pow_weightedScalar_eq_one hp5
  rw [← stickelbergerTwoResidueProduct_eq_weightedScalar hweight]
  exact hzero

/-- Named downstream consumer for a future Jacobi factorization module.
It assumes only the explicit symbol-weight interface and vanishing of the
fractional symbol on the corrected ideal; it does not assume that this ideal
is principal or generated by a Jacobi sum. -/
theorem jacobiStickelbergerTwoResidueConsumer
    (hp5 : 5 ≤ p) {eta : OK} {v : FinitePrime (PrimeCyclotomicField p)}
    (hweight : HasDirectCharacterSquareResidueWeightAt eta v)
    (hzero : fractionalPthPowerResidueSymbol eta
      (stickelbergerTwoPrimeIdeal v) = 1) :
    totalPthPowerResidueSymbolAtPrime eta v = 1 := by
  apply eq_one_of_pow_weightedScalar_eq_one hp5
  rw [← fractionalPthPowerResidueSymbol_stickelbergerTwoPrimeIdeal_eq_weightedScalar
    hweight]
  exact hzero

end NumberTheory.CyclotomicCharacter.InverseExtension
