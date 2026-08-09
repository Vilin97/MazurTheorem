/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.CyclotomicStickelbergerTwoResidue

/-!
# Residue weight of a normalized cyclotomic Kummer radicand

A Kummer radicand transforms through the square of the direct cyclotomic
character only up to a `p`-th power in the fraction field.  This file clears
that field-valued witness at one finite prime and proves the resulting
direct-character-square identity for total power-residue symbols.

The clearance uses Mathlib's
`IsDedekindDomain.HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer`.
No external reciprocity theorem is invoked here.
-/

open scoped NumberField nonZeroDivisors

namespace NumberTheory.CyclotomicCharacter.InverseExtension

universe u

variable {p : ℕ} [Fact p.Prime]
variable {L : Type u} [Field L] [NumberField L]
variable [Algebra (PrimeCyclotomicField p) L]
variable [IsScalarTower ℚ (PrimeCyclotomicField p) L]

local notation "K" => PrimeCyclotomicField p
local notation "OK" => NumberField.RingOfIntegers K

omit [Fact p.Prime] in
private theorem baseIntegerEquiv_one :
    baseIntegerEquiv (1 : Gal(K/ℚ)) = RingEquiv.refl OK := by
  apply RingEquiv.ext
  intro x
  apply NumberField.RingOfIntegers.ext
  change (1 : Gal(K/ℚ)) (x : K) = (x : K)
  simp

omit [Fact p.Prime] in
private theorem mapFinitePrime_one (v : FinitePrime K) :
    mapFinitePrime (1 : Gal(K/ℚ)) v = v := by
  apply IsDedekindDomain.HeightOneSpectrum.asIdeal_injective
  rw [mapFinitePrime_asIdeal, baseIntegerEquiv_one]
  change Ideal.map (RingHom.id OK) v.asIdeal = v.asIdeal
  exact v.asIdeal.map_id

omit [Fact p.Prime] in
private theorem rootsOfUnity_pow_prime_eq_one
    (x : rootsOfUnity p K) : x ^ p = 1 := by
  apply Subtype.ext
  exact x.property

private theorem totalPthPowerResidueSymbolAtPrime_pow_succ_of_not_mem
    (v : FinitePrime K) (eta : OK) (n : ℕ)
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

/-- Transporting a normalized integral representative gives a square-weight
Kummer equality with a field-valued `p`-th-power witness. -/
private theorem KummerPresentation.exists_normalized_map_eq_pow_mul_pow
    (E : InverseExtension p L) (P : KummerPresentation E)
    (eta : OK) (c : Kˣ)
    (heta : algebraMap OK K eta = P.radicand * (c : K) ^ p)
    (sigma : Gal(K/ℚ)) :
    ∃ w : K,
      algebraMap OK K (baseIntegerEquiv sigma eta) =
        (algebraMap OK K eta) ^
            (((directCharacter p sigma : (ZMod p)ˣ) : ZMod p).val *
              ((directCharacter p sigma : (ZMod p)ˣ) : ZMod p).val) *
          w ^ p := by
  let n := ((directCharacter p sigma : (ZMod p)ˣ) : ZMod p).val *
    ((directCharacter p sigma : (ZMod p)ˣ) : ZMod p).val
  obtain ⟨b, hb⟩ := P.exists_map_radicand_eq_pow_mul_pow E sigma
  refine ⟨b * sigma (c : K) / (c : K) ^ n, ?_⟩
  have hcpow : ((c : K) ^ p) ^ n = ((c : K) ^ n) ^ p := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm p n]
  calc
    algebraMap OK K (baseIntegerEquiv sigma eta) =
        IsFractionRing.ringEquivOfRingEquiv (baseIntegerEquiv sigma)
          (algebraMap OK K eta) := by
      rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
    _ = sigma (algebraMap OK K eta) := by
      rw [inducedBaseIntegerEquiv_eq]
      rfl
    _ = sigma (P.radicand * (c : K) ^ p) := by rw [heta]
    _ = sigma P.radicand * (sigma (c : K)) ^ p := by
      rw [map_mul, map_pow]
    _ = (P.radicand ^ n * b ^ p) * (sigma (c : K)) ^ p := by
      rw [hb]
    _ = (P.radicand * (c : K) ^ p) ^ n *
        (b * sigma (c : K) / (c : K) ^ n) ^ p := by
      rw [mul_pow, hcpow, div_pow, mul_pow]
      field_simp [Units.ne_zero c]
    _ = (algebraMap OK K eta) ^ n *
        (b * sigma (c : K) / (c : K) ^ n) ^ p := by rw [heta]

/-- Clear a field-valued `p`-th-power witness at a finite prime where both
integral representatives are units.  The resulting numerator and denominator
are themselves units at that prime. -/
private theorem exists_integral_cross_multiplier
    (v : FinitePrime K) (eta₀ eta : OK) (n : ℕ) (w : K)
    (heta₀ : eta₀ ∉ v.asIdeal) (heta : eta ∉ v.asIdeal)
    (hw : algebraMap OK K eta₀ =
      (algebraMap OK K eta) ^ n * w ^ p) :
    ∃ x : OK, ∃ d : v.asIdeal.primeCompl,
      x ∉ v.asIdeal ∧
        eta₀ * (d : OK) ^ p = eta ^ n * x ^ p := by
  have hwpow : (v.valuation K w) ^ p = 1 := by
    have hval := congrArg (v.valuation K) hw
    simpa only [map_mul, map_pow,
      v.valuation_eq_one_iff_notMem.mpr heta₀,
      v.valuation_eq_one_iff_notMem.mpr heta, one_pow, one_mul] using hval.symm
  have hwval : v.valuation K w = 1 :=
    (pow_eq_one_iff_of_nonneg bot_le (Fact.out : p.Prime).ne_zero).mp hwpow
  obtain ⟨x, d, hwd⟩ :=
    v.exists_primeCompl_mul_eq_of_integer w hwval.le
  have hdval : v.valuation K (algebraMap OK K (d : OK)) = 1 :=
    v.valuation_eq_one_iff_notMem.mpr d.prop
  have hxval : v.valuation K (algebraMap OK K x) = 1 := by
    rw [← hwd, map_mul, hwval, hdval, mul_one]
  refine ⟨x, d, v.valuation_eq_one_iff_notMem.mp hxval, ?_⟩
  apply IsFractionRing.injective OK K
  simp only [map_mul, map_pow]
  rw [hw, ← hwd, mul_pow]
  ring

/-- A normalized integral Kummer radicand has direct-character-square residue
weight at a finite prime when its whole Galois orbit avoids the numerator.

The orbitwise support condition is essential.  A field-valued Kummer witness
can have a denominator at a conjugate prime even when the original prime
avoids `eta`; clearing it locally needs both integral representatives to be
units at the transported prime. -/
theorem KummerPresentation.hasDirectCharacterSquareResidueWeightAt_of_normalization
    (E : InverseExtension p L) (P : KummerPresentation E)
    (eta : OK) (c : Kˣ)
    (hnormalization : algebraMap OK K eta =
      P.radicand * (c : K) ^ p)
    (v : FinitePrime K)
    (horbit : ∀ sigma : Gal(K/ℚ),
      eta ∉ (mapFinitePrime sigma v).asIdeal)
    (hpv : (p : OK) ∉ v.asIdeal) :
    HasDirectCharacterSquareResidueWeightAt eta v := by
  intro sigma
  let a : (ZMod p)ˣ := directCharacter p sigma
  let m : ℕ := (a : ZMod p).val
  let n : ℕ := m * m
  let r : ℕ := (((a ^ 2 : (ZMod p)ˣ)⁻¹ : (ZMod p)ˣ) : ZMod p).val
  let t : ℕ := ((a⁻¹ : (ZMod p)ˣ) : ZMod p).val
  have hm_pos : 0 < m := ZMod.val_pos.mpr (Units.ne_zero a)
  have hn_pos : 0 < n := Nat.mul_pos hm_pos hm_pos
  have heta : eta ∉ v.asIdeal := by
    simpa only [mapFinitePrime_one] using horbit (1 : Gal(K/ℚ))
  have hleft : baseIntegerEquiv sigma eta ∉
      (mapFinitePrime sigma v).asIdeal :=
    baseIntegerEquiv_not_mem_mapFinitePrime sigma v eta heta
  have heta_map : eta ∉ (mapFinitePrime sigma v).asIdeal := horbit sigma
  have hp_map : (p : OK) ∉ (mapFinitePrime sigma v).asIdeal :=
    prime_not_mem_mapFinitePrime sigma v hpv
  obtain ⟨w, hw₀⟩ :=
    P.exists_normalized_map_eq_pow_mul_pow E eta c hnormalization sigma
  have hw : algebraMap OK K (baseIntegerEquiv sigma eta) =
      (algebraMap OK K eta) ^ n * w ^ p := by
    simpa only [a, m, n] using hw₀
  obtain ⟨x, d, hx_map, hcross⟩ := exists_integral_cross_multiplier
    (v := mapFinitePrime sigma v) (eta₀ := baseIntegerEquiv sigma eta)
    (eta := eta) (n := n) (w := w) hleft heta_map hw
  have hd_pow_map : (d : OK) ^ p ∉ (mapFinitePrime sigma v).asIdeal := by
    intro hmem
    exact d.prop (((mapFinitePrime sigma v).isPrime.pow_mem_iff_mem p
      (Fact.out : p.Prime).pos).mp hmem)
  have heta_pow_map : eta ^ n ∉ (mapFinitePrime sigma v).asIdeal := by
    intro hmem
    exact heta_map (((mapFinitePrime sigma v).isPrime.pow_mem_iff_mem n
      hn_pos).mp hmem)
  have hx_pow_map : x ^ p ∉ (mapFinitePrime sigma v).asIdeal := by
    intro hmem
    exact hx_map (((mapFinitePrime sigma v).isPrime.pow_mem_iff_mem p
      (Fact.out : p.Prime).pos).mp hmem)
  let x₀ := totalPthPowerResidueSymbolAtPrime eta v
  let y := totalPthPowerResidueSymbolAtPrime eta (mapFinitePrime sigma v)
  have hcov : totalPthPowerResidueSymbolAtPrime
      (baseIntegerEquiv sigma eta) (mapFinitePrime sigma v) = x₀ ^ m := by
    simpa only [a, m, x₀] using
      totalPthPowerResidueSymbolAtPrime_mapFinitePrime sigma v eta
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn_pos.ne'
  have hpow_eta : totalPthPowerResidueSymbolAtPrime (eta ^ n)
      (mapFinitePrime sigma v) = y ^ n := by
    rw [hk]
    exact totalPthPowerResidueSymbolAtPrime_pow_succ_of_not_mem
      (mapFinitePrime sigma v) eta k heta_map hp_map
  have hsymbols := congrArg
    (fun z : OK => totalPthPowerResidueSymbolAtPrime z
      (mapFinitePrime sigma v)) hcross
  rw [totalPthPowerResidueSymbolAtPrime_mul_of_not_mem
      (mapFinitePrime sigma v) (baseIntegerEquiv sigma eta) ((d : OK) ^ p)
      hleft hd_pow_map hp_map,
    totalPthPowerResidueSymbolAtPrime_pow_prime_eq_one, mul_one,
    totalPthPowerResidueSymbolAtPrime_mul_of_not_mem
      (mapFinitePrime sigma v) (eta ^ n) (x ^ p)
      heta_pow_map hx_pow_map hp_map,
    hpow_eta, totalPthPowerResidueSymbolAtPrime_pow_prime_eq_one, mul_one]
      at hsymbols
  have hclass : y ^ n = x₀ ^ m := by
    rw [hcov] at hsymbols
    exact hsymbols.symm
  have hraised : y ^ (n * r) = x₀ ^ (m * r) := by
    calc
      y ^ (n * r) = (y ^ n) ^ r := pow_mul y n r
      _ = (x₀ ^ m) ^ r := congrArg (fun z => z ^ r) hclass
      _ = x₀ ^ (m * r) := (pow_mul x₀ m r).symm
  have hn_mod : n * r ≡ 1 [MOD p] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    simp only [n, m, r, Nat.cast_mul, ZMod.natCast_zmod_val, Nat.cast_one]
    rw [← Units.val_mul, ← Units.val_mul]
    simp [pow_two]
  have hm_mod : m * r ≡ t [MOD p] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    simp only [m, r, t, Nat.cast_mul, ZMod.natCast_zmod_val]
    change (a : ZMod p) * ((a ^ 2)⁻¹ : (ZMod p)ˣ) = (a⁻¹ : (ZMod p)ˣ)
    rw [← Units.val_mul]
    congr 1
    group
  have hy_prime : y ^ p = 1 := rootsOfUnity_pow_prime_eq_one y
  have hx_prime : x₀ ^ p = 1 := rootsOfUnity_pow_prime_eq_one x₀
  calc
    y = y ^ (n * r) := by
      rw [pow_eq_pow_of_modEq hn_mod hy_prime, pow_one]
    _ = x₀ ^ (m * r) := hraised
    _ = x₀ ^ t := pow_eq_pow_of_modEq hm_mod hx_prime

end NumberTheory.CyclotomicCharacter.InverseExtension
