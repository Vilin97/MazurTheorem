/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.CyclotomicOrbitCoprimeNormalization
import MazurTorsion.NumberTheory.CyclotomicNormalizedResidueWeight
import MazurTorsion.NumberTheory.CyclotomicResidueOrbitFaithful
import MazurTorsion.NumberTheory.CyclotomicJacobiIdealFaithful

/-!
# Reduction of the cyclotomic Kummer product to a faithful Jacobi leaf

For an orbit-coprime integral normalization `eta`, every prime in the
denominator has direct-character-square residue weight.  A nonfaithful
cyclotomic orbit therefore has trivial residue symbol.  On a faithful orbit,
the checked factorization of the conjugate diagonal Jacobi sum identifies its
principal ideal with the corrected Stickelberger-two prime ideal.  The
Stickelberger scalar calculation then reduces triviality at the base prime to
one explicit value of the residue-symbol homomorphism.

The last value is retained below as a pointwise theorem hypothesis.  Thus this
file is a reduction of the integral Kummer product, not a reciprocity theorem.
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
private theorem baseIntegerEquiv_one_for_reduction :
    baseIntegerEquiv (1 : Gal(K/ℚ)) = RingEquiv.refl OK := by
  apply RingEquiv.ext
  intro x
  apply NumberField.RingOfIntegers.ext
  change (1 : Gal(K/ℚ)) (x : K) = (x : K)
  simp

omit [Fact p.Prime] in
private theorem mem_of_integralPrincipalDivisor_support
    (a : OK) (ha : a ≠ 0) (v : FinitePrime K)
    (hv :
      NumberTheory.UnramifiedArtin.fractionalIdealDivisor OK K
        (Additive.ofMul
          (toPrincipalIdeal OK K
            (Units.mk0
              (algebraMap OK K a)
              (by
                simpa only [map_zero] using
                  (IsFractionRing.injective OK K).ne ha)))) v ≠ 0) :
    a ∈ v.asIdeal := by
  have hvcount :
      FractionalIdeal.count K v
        (FractionalIdeal.spanSingleton OK⁰ (algebraMap OK K a)) ≠ 0 := by
    rw [NumberTheory.UnramifiedArtin.fractionalIdealDivisor_apply] at hv
    rw [toMul_ofMul, coe_toPrincipalIdeal, Units.val_mk0] at hv
    exact hv
  have hspan : Ideal.span {a} ≠ ⊥ :=
    Ideal.span_singleton_eq_bot.not.mpr ha
  have hvcount' :
      ((Associates.mk v.asIdeal).count
        (Associates.mk (Ideal.span {a})).factors : ℤ) ≠ 0 := by
    rw [← FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.count_coe K v hspan] at hvcount
    exact hvcount
  have hvcountNat :
      (Associates.mk v.asIdeal).count
        (Associates.mk (Ideal.span {a})).factors ≠ 0 := by
    exact_mod_cast hvcount'
  have hvdvd : v.asIdeal ∣ Ideal.span {a} :=
    (Associates.count_ne_zero_iff_dvd hspan v.irreducible).mp hvcountNat
  exact (Ideal.dvd_span_singleton).mp hvdvd

private theorem isCoprime_cyclotomicPrime_of_not_mem_for_reduction
    (a : OK) (ha : a ∉ (cyclotomicPrime p).asIdeal) :
    IsCoprime (Ideal.span {a}) (cyclotomicPrime p).asIdeal := by
  rw [Ideal.isCoprime_iff_codisjoint, codisjoint_comm]
  apply ((cyclotomicPrime p).isMaximal.out.not_le_iff_codisjoint).mp
  intro hle
  exact ha ((Ideal.span_singleton_le_iff_mem
    (cyclotomicPrime p).asIdeal).mp hle)

private theorem cyclotomicJacobiSumTwo_complexConj_ne_zero_for_reduction
    (hp5 : 5 ≤ p) (v : FinitePrime K) (hpv : (p : OK) ∉ v.asIdeal) :
    cyclotomicIntegerComplexConj p (by omega)
      (cyclotomicJacobiSumTwo v hpv) ≠ 0 := by
  simpa only [map_zero] using
    (cyclotomicIntegerComplexConj p (by omega)).injective.ne
      (cyclotomicJacobiSumTwo_ne_zero (by omega) v hpv)

/-- For fixed orbit-coprime normalized data, the integral Kummer product is
trivial if the residue symbol of `eta` is trivial on the principal conjugate
diagonal Jacobi sum at every faithful denominator prime away from `p`.

The final argument is deliberately a pointwise hypothesis.  It is the sole
reciprocity input left by this reduction. -/
theorem KummerPresentation.integralPrincipalProduct_eq_one_of_faithfulJacobi
    (hp5 : 5 ≤ p) (E : InverseExtension p L) (P : KummerPresentation E)
    (eta a : OK) (ha : a ≠ 0) (c : Kˣ)
    (hnormalization : algebraMap OK K eta =
      P.radicand * (c : K) ^ p)
    (hcoprimeEtaA : IsCoprime (Ideal.span {eta}) (Ideal.span {a}))
    (hcoprimeAPrime :
      IsCoprime (Ideal.span {a}) (cyclotomicPrime p).asIdeal)
    (horbit : ∀ (sigma : Gal(K/ℚ)) (v : FinitePrime K),
      v.asIdeal ∣ Ideal.span {a} →
        eta ∉ (mapFinitePrime sigma v).asIdeal)
    (hfaithfulJacobi : ∀ (v : FinitePrime K)
      (_hvdiv : v.asIdeal ∣ Ideal.span {a})
      (hpv : (p : OK) ∉ v.asIdeal)
      (_hinjective : Function.Injective (fun b : (ZMod p)ˣ =>
        mapFinitePrime (galoisOfDirectCharacter b) v)),
      fractionalPthPowerResidueSymbol eta
        (toPrincipalIdeal OK K
          (Units.mk0
            (algebraMap OK K
              (cyclotomicIntegerComplexConj p (by omega)
                (cyclotomicJacobiSumTwo v hpv)))
            ((IsFractionRing.injective OK K).ne
              (cyclotomicJacobiSumTwo_complexConj_ne_zero_for_reduction
                hp5 v hpv)))) = 1) :
    P.fractionalKummerSymbol E
      (toPrincipalIdeal OK K
        (Units.mk0 (algebraMap OK K a)
          ((IsFractionRing.injective OK K).ne ha))) = 1 := by
  rw [P.fractionalKummerSymbol_integralPrincipal_eq_residueProduct
    E eta a ha c hnormalization hcoprimeEtaA hcoprimeAPrime,
    fractionalPthPowerResidueSymbol_apply]
  apply Finset.prod_eq_one
  intro v hv
  have hvCoefficient :
      NumberTheory.UnramifiedArtin.fractionalIdealDivisor OK K
        (Additive.ofMul
          (toPrincipalIdeal OK K
            (Units.mk0 (algebraMap OK K a)
              ((IsFractionRing.injective OK K).ne ha)))) v ≠ 0 :=
    Finsupp.mem_support_iff.mp hv
  have hav : a ∈ v.asIdeal :=
    mem_of_integralPrincipalDivisor_support a ha v hvCoefficient
  have hvdiv : v.asIdeal ∣ Ideal.span {a} :=
    Ideal.dvd_span_singleton.mpr hav
  by_cases hpv : (p : OK) ∈ v.asIdeal
  · simp [totalPthPowerResidueSymbolAtPrime_of_prime_mem eta v hpv]
  · have hweight : HasDirectCharacterSquareResidueWeightAt eta v :=
      P.hasDirectCharacterSquareResidueWeightAt_of_normalization
        E eta c hnormalization v (fun sigma => horbit sigma v hvdiv) hpv
    have hsymbol : totalPthPowerResidueSymbolAtPrime eta v = 1 := by
      by_cases hinjective : Function.Injective (fun b : (ZMod p)ˣ =>
          mapFinitePrime (galoisOfDirectCharacter b) v)
      · have hprincipal :=
          toPrincipalIdeal_cyclotomicJacobiSumTwo_complexConj_eq_stickelbergerTwoPrimeIdeal
            hp5 v hpv hinjective
        apply jacobiStickelbergerTwoResidueConsumer hp5 hweight
        rw [← hprincipal]
        exact hfaithfulJacobi v hvdiv hpv hinjective
      · exact totalPthPowerResidueSymbolAtPrime_eq_one_of_not_injective_orbit
          hweight hinjective
    simp [hsymbol]

/-- Every nonzero denominator away from the cyclotomic prime admits an
orbit-coprime pseudo-unit normalization for which the integral Kummer product
is reduced to the faithful-prime Jacobi-symbol values displayed explicitly
in the implication below. -/
theorem KummerPresentation.exists_orbitCoprime_normalization_reducing_integralProduct_to_faithfulJacobi
    (hp5 : 5 ≤ p) (E : InverseExtension p L)
    (hdiv : ∀ v : FinitePrime K,
      (p : ℤ) ∣ FractionalIdeal.count K v
        (FractionalIdeal.spanSingleton (nonZeroDivisors OK)
          E.kummerPresentation.radicand))
    (a : OK) (ha : a ≠ 0)
    (haPrime : a ∉ (cyclotomicPrime p).asIdeal) :
    ∃ (c : Kˣ) (eta : OK) (B : Ideal OK),
      eta ≠ 0 ∧
      algebraMap OK K eta = E.kummerPresentation.radicand * (c : K) ^ p ∧
      Ideal.span {eta} = B ^ p ∧
      IsCoprime (Ideal.span {eta})
        (galoisOrbitIdealProduct (Ideal.span {a})) ∧
      IsCoprime (Ideal.span {eta}) (cyclotomicPrime p).asIdeal ∧
      (∀ (sigma : Gal(K/ℚ)) (v : FinitePrime K),
        v.asIdeal ∣ Ideal.span {a} →
          eta ∉ (mapFinitePrime sigma v).asIdeal) ∧
      ((∀ (v : FinitePrime K)
        (_hvdiv : v.asIdeal ∣ Ideal.span {a})
        (hpv : (p : OK) ∉ v.asIdeal)
        (_hinjective : Function.Injective (fun b : (ZMod p)ˣ =>
          mapFinitePrime (galoisOfDirectCharacter b) v)),
        fractionalPthPowerResidueSymbol eta
          (toPrincipalIdeal OK K
            (Units.mk0
              (algebraMap OK K
                (cyclotomicIntegerComplexConj p (by omega)
                  (cyclotomicJacobiSumTwo v hpv)))
              ((IsFractionRing.injective OK K).ne
                (cyclotomicJacobiSumTwo_complexConj_ne_zero_for_reduction
                  hp5 v hpv)))) = 1) →
        E.kummerPresentation.fractionalKummerSymbol E
          (toPrincipalIdeal OK K
            (Units.mk0 (algebraMap OK K a)
              ((IsFractionRing.injective OK K).ne ha))) = 1) := by
  have hspanA : Ideal.span {a} ≠ ⊥ :=
    Ideal.span_singleton_eq_bot.not.mpr ha
  obtain ⟨c, eta, B, heta, hnormalization, hspan, hcoprimeOrbit,
      hcoprimePrime, horbit⟩ :=
    exists_galoisOrbit_coprime_integral_pseudoUnit_normalization
      E hdiv (Ideal.span {a}) hspanA
  refine ⟨c, eta, B, heta, hnormalization, hspan, hcoprimeOrbit,
    hcoprimePrime, horbit, ?_⟩
  intro hfaithfulJacobi
  have hcoprimeEtaAMapped :
      IsCoprime (Ideal.span {eta})
        (Ideal.map (baseIntegerEquiv (1 : Gal(K/ℚ))) (Ideal.span {a})) :=
    hcoprimeOrbit.of_prod_right (1 : Gal(K/ℚ))
      (Finset.mem_univ (1 : Gal(K/ℚ)))
  have hmapOne :
      Ideal.map (baseIntegerEquiv (1 : Gal(K/ℚ))) (Ideal.span {a}) =
        Ideal.span {a} := by
    rw [baseIntegerEquiv_one_for_reduction]
    exact Ideal.map_id (Ideal.span {a})
  have hcoprimeEtaA :
      IsCoprime (Ideal.span {eta}) (Ideal.span {a}) := by
    rwa [hmapOne] at hcoprimeEtaAMapped
  exact E.kummerPresentation.integralPrincipalProduct_eq_one_of_faithfulJacobi hp5 E
    eta a ha c hnormalization hcoprimeEtaA
      (isCoprime_cyclotomicPrime_of_not_mem_for_reduction a haPrime)
      horbit hfaithfulJacobi

end NumberTheory.CyclotomicCharacter.InverseExtension
