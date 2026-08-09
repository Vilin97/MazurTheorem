/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.CyclotomicPseudoUnitNormalization

/-!
# Galois-orbit coprime normalization of cyclotomic pseudo-units

This file strengthens the denominator-avoidance part of pseudo-unit
normalization.  Given a nonzero integral denominator ideal, we apply the
existing normalization theorem to the product of all of its cyclotomic
Galois conjugates.  The resulting numerator is therefore outside every
Galois conjugate of every finite prime dividing the denominator.

This is an ideal-theoretic normalization statement.  It does not use or
assert any reciprocity law.
-/

open scoped NumberField nonZeroDivisors

namespace NumberTheory.CyclotomicCharacter.InverseExtension

universe u

variable {p : ℕ} [Fact p.Prime]
variable {L : Type u} [Field L] [NumberField L]
variable [Algebra (PrimeCyclotomicField p) L]
variable [IsScalarTower ℚ (PrimeCyclotomicField p) L]

/-- The product of all cyclotomic Galois conjugates of an integral ideal. -/
noncomputable def galoisOrbitIdealProduct
    (I : Ideal
      (NumberField.RingOfIntegers (PrimeCyclotomicField p))) :
    Ideal (NumberField.RingOfIntegers (PrimeCyclotomicField p)) :=
  ∏ sigma : Gal(PrimeCyclotomicField p/ℚ),
    Ideal.map (baseIntegerEquiv sigma) I

omit [Fact p.Prime] in
/-- The Galois-orbit product of a nonzero ideal is nonzero. -/
theorem galoisOrbitIdealProduct_ne_bot
    (I : Ideal
      (NumberField.RingOfIntegers (PrimeCyclotomicField p)))
    (hI : I ≠ ⊥) :
    galoisOrbitIdealProduct I ≠ ⊥ := by
  classical
  unfold galoisOrbitIdealProduct
  exact Finset.prod_ne_zero_iff.mpr fun sigma _ =>
    (Ideal.map_eq_bot_iff_of_injective
      (baseIntegerEquiv sigma).injective).not.mpr hI

omit [Fact p.Prime] in
/-- Coprimality with the full orbit product keeps an element outside every
conjugate of every finite prime dividing the original ideal. -/
theorem not_mem_mapFinitePrime_of_coprime_galoisOrbitIdealProduct
    (I : Ideal
      (NumberField.RingOfIntegers (PrimeCyclotomicField p)))
    (eta : NumberField.RingOfIntegers (PrimeCyclotomicField p))
    (hcoprime :
      IsCoprime (Ideal.span {eta}) (galoisOrbitIdealProduct I))
    (sigma : Gal(PrimeCyclotomicField p/ℚ))
    (v : FinitePrime (PrimeCyclotomicField p))
    (hvI : v.asIdeal ∣ I) :
    eta ∉ (mapFinitePrime sigma v).asIdeal := by
  have hcoprime_map :
      IsCoprime (Ideal.span {eta})
        (Ideal.map (baseIntegerEquiv sigma) I) := by
    exact hcoprime.of_prod_right sigma (Finset.mem_univ sigma)
  obtain ⟨J, hJ⟩ := hvI
  have hmap_dvd :
      Ideal.map (baseIntegerEquiv sigma) v.asIdeal ∣
        Ideal.map (baseIntegerEquiv sigma) I := by
    refine ⟨Ideal.map (baseIntegerEquiv sigma) J, ?_⟩
    rw [← Ideal.map_mul, hJ]
  have hcoprime_prime :
      IsCoprime (Ideal.span {eta})
        (mapFinitePrime sigma v).asIdeal := by
    rw [mapFinitePrime_asIdeal]
    exact hcoprime_map.of_isCoprime_of_dvd_right hmap_dvd
  intro heta
  apply (mapFinitePrime sigma v).isPrime.ne_top
  apply top_unique
  rw [← hcoprime_prime.sup_eq]
  exact sup_le
    ((Ideal.span_singleton_le_iff_mem
      (mapFinitePrime sigma v).asIdeal).mpr heta)
    le_rfl

/-- A pseudo-unit radicand can be normalized so that its integral numerator
is coprime to the full Galois-orbit product of a prescribed nonzero
denominator ideal.  In particular, the numerator lies outside every
conjugate of every finite prime dividing that denominator. -/
theorem exists_galoisOrbit_coprime_integral_pseudoUnit_normalization
    (E : InverseExtension p L)
    (hdiv : ∀ v : FinitePrime (PrimeCyclotomicField p),
      (p : ℤ) ∣ FractionalIdeal.count (PrimeCyclotomicField p) v
        (FractionalIdeal.spanSingleton
          (nonZeroDivisors
            (NumberField.RingOfIntegers (PrimeCyclotomicField p)))
          E.kummerPresentation.radicand))
    (I : Ideal
      (NumberField.RingOfIntegers (PrimeCyclotomicField p)))
    (hI : I ≠ ⊥) :
    ∃ (c : (PrimeCyclotomicField p)ˣ)
        (eta : NumberField.RingOfIntegers (PrimeCyclotomicField p))
        (B : Ideal
          (NumberField.RingOfIntegers (PrimeCyclotomicField p))),
      eta ≠ 0 ∧
      algebraMap
          (NumberField.RingOfIntegers (PrimeCyclotomicField p))
          (PrimeCyclotomicField p) eta =
        E.kummerPresentation.radicand *
          (c : PrimeCyclotomicField p) ^ p ∧
      Ideal.span {eta} = B ^ p ∧
      IsCoprime (Ideal.span {eta}) (galoisOrbitIdealProduct I) ∧
      IsCoprime (Ideal.span {eta}) (cyclotomicPrime p).asIdeal ∧
      ∀ (sigma : Gal(PrimeCyclotomicField p/ℚ))
          (v : FinitePrime (PrimeCyclotomicField p)),
        v.asIdeal ∣ I → eta ∉ (mapFinitePrime sigma v).asIdeal := by
  obtain ⟨c, eta, B, heta, hc, hspan, hcoprime, hprime⟩ :=
    E.exists_coprime_integral_pseudoUnit_normalization hdiv
      (galoisOrbitIdealProduct I)
      (galoisOrbitIdealProduct_ne_bot I hI)
  refine ⟨c, eta, B, heta, hc, hspan, hcoprime, hprime, ?_⟩
  intro sigma v hvI
  exact not_mem_mapFinitePrime_of_coprime_galoisOrbitIdealProduct
    I eta hcoprime sigma v hvI

end NumberTheory.CyclotomicCharacter.InverseExtension
