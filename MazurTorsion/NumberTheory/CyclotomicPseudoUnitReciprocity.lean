/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.CyclotomicKummer

/-!
# One-sided reciprocity for cyclotomic pseudo-units

This file isolates the arithmetic core of one-sided Kummer reciprocity in
the canonical Kummer presentation of an inverse-cyclotomic extension.  The
symbol used below is the raw finite-prime Frobenius product, followed by the
canonical Kummer coordinate; no class-field-theory or reciprocity hypothesis
is bundled into its definition.
-/

open scoped NumberField nonZeroDivisors

namespace NumberTheory.CyclotomicCharacter.InverseExtension

universe u

variable {p : ℕ} [Fact p.Prime]
variable {L : Type u} [Field L] [NumberField L]
variable [Algebra (PrimeCyclotomicField p) L]
variable [IsScalarTower ℚ (PrimeCyclotomicField p) L]

/-- The raw Kummer/Frobenius product is the cyclic Artin product followed by
the coordinate supplied by the canonical Kummer presentation. -/
theorem rawKummerSymbol_eq_coordinate_comp (E : InverseExtension p L) :
    NumberTheory.UnramifiedArtin.fractionalIdealHom
        (fun v =>
          (E.galEquiv.symm.trans (E.kummerPresentation.pairing E))
            (E.artinSymbol v)) =
      (E.galEquiv.symm.trans
        (E.kummerPresentation.pairing E)).toMonoidHom.comp
        E.fractionalArtin := by
  change NumberTheory.UnramifiedArtin.fractionalIdealHom
      (fun v =>
        (E.galEquiv.symm.trans (E.kummerPresentation.pairing E))
          (E.artinSymbol v)) =
    (E.galEquiv.symm.trans
      (E.kummerPresentation.pairing E)).toMonoidHom.comp
      (NumberTheory.UnramifiedArtin.fractionalIdealHom E.artinSymbol)
  exact (NumberTheory.UnramifiedArtin.fractionalIdealHom_comp
    (E.galEquiv.symm.trans
      (E.kummerPresentation.pairing E)).toMonoidHom E.artinSymbol).symm

/-- Vanishing of the raw Kummer/Frobenius product is equivalent to vanishing
of the same finite-prime product in the cyclic coordinate. -/
theorem rawKummerSymbol_eq_one_iff (E : InverseExtension p L)
    (I : (FractionalIdeal
      (nonZeroDivisors
        (NumberField.RingOfIntegers (PrimeCyclotomicField p)))
      (PrimeCyclotomicField p))ˣ) :
    NumberTheory.UnramifiedArtin.fractionalIdealHom
        (fun v =>
          (E.galEquiv.symm.trans (E.kummerPresentation.pairing E))
            (E.artinSymbol v)) I = 1 ↔
      E.fractionalArtin I = 1 := by
  rw [E.rawKummerSymbol_eq_coordinate_comp]
  change (E.galEquiv.symm.trans (E.kummerPresentation.pairing E))
      (E.fractionalArtin I) = 1 ↔ E.fractionalArtin I = 1
  constructor
  · intro h
    apply (E.galEquiv.symm.trans
      (E.kummerPresentation.pairing E)).injective
    simpa using h
  · intro h
    rw [h]
    exact map_one _

/-- The divisor root already defined by the canonical Kummer presentation
has the expected `p`-th power whenever all radicand exponents are divisible
by `p`.  This formulation uses exactly the pseudo-unit hypothesis, without
an unramifiedness assumption. -/
theorem unramifiedRadicandIdealRoot_pow_eq_of_dvd_counts
    (E : InverseExtension p L)
    (hdiv : ∀ v : FinitePrime (PrimeCyclotomicField p),
      (p : ℤ) ∣ FractionalIdeal.count (PrimeCyclotomicField p) v
        (FractionalIdeal.spanSingleton
          (nonZeroDivisors
            (NumberField.RingOfIntegers (PrimeCyclotomicField p)))
          E.kummerPresentation.radicand)) :
    E.unramifiedRadicandIdealRoot ^ p =
      FractionalIdeal.spanSingleton
        (nonZeroDivisors
          (NumberField.RingOfIntegers (PrimeCyclotomicField p)))
        E.kummerPresentation.radicand := by
  let I : FractionalIdeal
      (nonZeroDivisors
        (NumberField.RingOfIntegers (PrimeCyclotomicField p)))
      (PrimeCyclotomicField p) :=
    FractionalIdeal.spanSingleton
      (nonZeroDivisors
        (NumberField.RingOfIntegers (PrimeCyclotomicField p)))
      E.kummerPresentation.radicand
  let exps : FinitePrime (PrimeCyclotomicField p) → ℤ := fun v ↦
    FractionalIdeal.count (PrimeCyclotomicField p) v I / (p : ℤ)
  have hexps : ∀ᶠ v : FinitePrime (PrimeCyclotomicField p) in Filter.cofinite,
      exps v = 0 :=
    (FractionalIdeal.finite_factors I).mono fun v hv ↦ by simp [exps, hv]
  have hI_ne : I ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.mpr
      (E.kummerPresentation.radicand_ne_zero E)
  change E.unramifiedRadicandIdealRoot ^ p = I
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization'
      (PrimeCyclotomicField p)
      (pow_ne_zero p E.unramifiedRadicandIdealRoot_ne_zero),
    ← FractionalIdeal.finprod_heightOneSpectrum_factorization'
      (PrimeCyclotomicField p) hI_ne]
  apply finprod_congr
  intro v
  apply congrArg
  rw [FractionalIdeal.count_pow,
    show FractionalIdeal.count (PrimeCyclotomicField p) v
        E.unramifiedRadicandIdealRoot = exps v by
      simpa only [unramifiedRadicandIdealRoot, exps, I] using
        FractionalIdeal.count_finprod
          (PrimeCyclotomicField p) v exps hexps]
  exact Int.mul_ediv_cancel' (hdiv v)

/-- Unit-valued form of the pseudo-unit divisor-root identity. -/
theorem unramifiedRadicandRootIdeal_pow_eq_of_dvd_counts
    (E : InverseExtension p L)
    (hdiv : ∀ v : FinitePrime (PrimeCyclotomicField p),
      (p : ℤ) ∣ FractionalIdeal.count (PrimeCyclotomicField p) v
        (FractionalIdeal.spanSingleton
          (nonZeroDivisors
            (NumberField.RingOfIntegers (PrimeCyclotomicField p)))
          E.kummerPresentation.radicand)) :
    E.unramifiedRadicandRootIdeal ^ p =
      toPrincipalIdeal
        (NumberField.RingOfIntegers (PrimeCyclotomicField p))
        (PrimeCyclotomicField p)
        (Units.mk0 E.kummerPresentation.radicand
          (E.kummerPresentation.radicand_ne_zero E)) := by
  apply Units.ext
  simpa only [unramifiedRadicandRootIdeal, Units.val_pow_eq_pow_val,
    Units.val_mk0, coe_toPrincipalIdeal] using
    E.unramifiedRadicandIdealRoot_pow_eq_of_dvd_counts hdiv

/-- Every value of the raw canonical Kummer/Frobenius symbol has exponent
dividing `p`, because its target is the group of `p`-th roots of unity. -/
theorem rawKummerSymbol_pow_eq_one (E : InverseExtension p L)
    (I : (FractionalIdeal
      (nonZeroDivisors
        (NumberField.RingOfIntegers (PrimeCyclotomicField p)))
      (PrimeCyclotomicField p))ˣ) :
    (NumberTheory.UnramifiedArtin.fractionalIdealHom
      (fun v =>
        (E.galEquiv.symm.trans (E.kummerPresentation.pairing E))
          (E.artinSymbol v)) I) ^ p = 1 := by
  apply Subtype.ext
  exact (NumberTheory.UnramifiedArtin.fractionalIdealHom
    (fun v =>
      (E.galEquiv.symm.trans (E.kummerPresentation.pairing E))
        (E.artinSymbol v)) I).2

/-- Consequently, the raw canonical Kummer/Frobenius symbol kills every
`p`-th power in the fractional-ideal group. -/
theorem rawKummerSymbol_pow_ideal_eq_one (E : InverseExtension p L)
    (I : (FractionalIdeal
      (nonZeroDivisors
        (NumberField.RingOfIntegers (PrimeCyclotomicField p)))
      (PrimeCyclotomicField p))ˣ) :
    NumberTheory.UnramifiedArtin.fractionalIdealHom
        (fun v =>
          (E.galEquiv.symm.trans (E.kummerPresentation.pairing E))
            (E.artinSymbol v)) (I ^ p) = 1 := by
  rw [map_pow]
  exact E.rawKummerSymbol_pow_eq_one I

/-- The pseudo-unit divisor condition alone makes the raw symbol vanish on
the principal fractional ideal of the canonical radicand.  The missing
one-sided reciprocity theorem is the distinct assertion with an arbitrary
principal ideal in the denominator slot. -/
theorem rawKummerSymbol_principalRadicand_eq_one_of_dvd_counts
    (E : InverseExtension p L)
    (hdiv : ∀ v : FinitePrime (PrimeCyclotomicField p),
      (p : ℤ) ∣ FractionalIdeal.count (PrimeCyclotomicField p) v
        (FractionalIdeal.spanSingleton
          (nonZeroDivisors
            (NumberField.RingOfIntegers (PrimeCyclotomicField p)))
          E.kummerPresentation.radicand)) :
    NumberTheory.UnramifiedArtin.fractionalIdealHom
        (fun v =>
          (E.galEquiv.symm.trans (E.kummerPresentation.pairing E))
            (E.artinSymbol v))
      (toPrincipalIdeal
        (NumberField.RingOfIntegers (PrimeCyclotomicField p))
        (PrimeCyclotomicField p)
        (Units.mk0 E.kummerPresentation.radicand
          (E.kummerPresentation.radicand_ne_zero E))) = 1 := by
  rw [← E.unramifiedRadicandRootIdeal_pow_eq_of_dvd_counts hdiv]
  exact E.rawKummerSymbol_pow_ideal_eq_one E.unramifiedRadicandRootIdeal

end NumberTheory.CyclotomicCharacter.InverseExtension
