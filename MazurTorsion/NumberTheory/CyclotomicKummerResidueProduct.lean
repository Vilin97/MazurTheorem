/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.CyclotomicKummerResidueSymbol
import MazurTorsion.NumberTheory.CyclotomicPseudoUnitNormalization
import MazurTorsion.NumberTheory.KummerArtinProduct

/-!
# Finite residue products for normalized cyclotomic pseudo-units

This file extends the direct prime power-residue symbol to a total family of
local symbols and then to nonzero fractional ideals.  The total symbol is
defined to be one at primes dividing its numerator or the rational prime
\`p\`; away from those primes it is the direct finite-field symbol.

For a normalized pseudo-unit \`η\` with \`(η) = B ^ p\`, the resulting product
is trivial on \`(η)\`.  For a principal denominator \`(a)\` coprime to both \`η\`
and the cyclotomic prime, the Kummer--Frobenius product is identified with
the product having numerator \`η\`.  Thus the integral Kummer target is
reduced, by checked equivalences, to equality of the two oppositely oriented
finite residue products.  No equality of those products is assumed here.
-/

open scoped NumberField nonZeroDivisors

namespace NumberTheory.CyclotomicCharacter.InverseExtension

universe u

variable {p : ℕ} [Fact p.Prime]
variable {L : Type u} [Field L] [NumberField L]
variable [Algebra (PrimeCyclotomicField p) L]
variable [IsScalarTower ℚ (PrimeCyclotomicField p) L]

/-- A total prime-level power-residue symbol.  At primes where the usual
symbol is undefined because the numerator or \`p\` vanishes, its value is set
to one. -/
noncomputable def totalPthPowerResidueSymbolAtPrime
    (η : NumberField.RingOfIntegers (PrimeCyclotomicField p))
    (v : FinitePrime (PrimeCyclotomicField p)) :
    rootsOfUnity p (PrimeCyclotomicField p) := by
  classical
  exact if hηv : η ∈ v.asIdeal then 1
    else if hpv :
        (p : NumberField.RingOfIntegers (PrimeCyclotomicField p)) ∈
          v.asIdeal then 1
    else pthPowerResidueSymbolAtPrime v η hηv hpv

@[simp]
theorem totalPthPowerResidueSymbolAtPrime_of_numerator_mem
    (η : NumberField.RingOfIntegers (PrimeCyclotomicField p))
    (v : FinitePrime (PrimeCyclotomicField p))
    (hηv : η ∈ v.asIdeal) :
    totalPthPowerResidueSymbolAtPrime η v = 1 := by
  simp [totalPthPowerResidueSymbolAtPrime, hηv]

@[simp]
theorem totalPthPowerResidueSymbolAtPrime_of_prime_mem
    (η : NumberField.RingOfIntegers (PrimeCyclotomicField p))
    (v : FinitePrime (PrimeCyclotomicField p))
    (hpv : (p : NumberField.RingOfIntegers (PrimeCyclotomicField p)) ∈
      v.asIdeal) :
    totalPthPowerResidueSymbolAtPrime η v = 1 := by
  by_cases hηv : η ∈ v.asIdeal
  · exact totalPthPowerResidueSymbolAtPrime_of_numerator_mem η v hηv
  · simp [totalPthPowerResidueSymbolAtPrime, hηv, hpv]

theorem totalPthPowerResidueSymbolAtPrime_of_not_mem
    (η : NumberField.RingOfIntegers (PrimeCyclotomicField p))
    (v : FinitePrime (PrimeCyclotomicField p))
    (hηv : η ∉ v.asIdeal)
    (hpv : (p : NumberField.RingOfIntegers (PrimeCyclotomicField p)) ∉
      v.asIdeal) :
    totalPthPowerResidueSymbolAtPrime η v =
      pthPowerResidueSymbolAtPrime v η hηv hpv := by
  simp [totalPthPowerResidueSymbolAtPrime, hηv, hpv]

/-- The finite product of total prime power-residue symbols over a nonzero
fractional ideal. -/
noncomputable def fractionalPthPowerResidueSymbol
    (η : NumberField.RingOfIntegers (PrimeCyclotomicField p)) :
    (FractionalIdeal
      (nonZeroDivisors
        (NumberField.RingOfIntegers (PrimeCyclotomicField p)))
      (PrimeCyclotomicField p))ˣ →*
        rootsOfUnity p (PrimeCyclotomicField p) :=
  NumberTheory.UnramifiedArtin.fractionalIdealHom
    (totalPthPowerResidueSymbolAtPrime η)

@[simp]
theorem fractionalPthPowerResidueSymbol_prime
    (η : NumberField.RingOfIntegers (PrimeCyclotomicField p))
    (v : FinitePrime (PrimeCyclotomicField p)) :
    fractionalPthPowerResidueSymbol η
      (NumberTheory.UnramifiedArtin.primeFractionalIdealUnit
        (K := PrimeCyclotomicField p) v) =
      totalPthPowerResidueSymbolAtPrime η v :=
  NumberTheory.UnramifiedArtin.fractionalIdealHom_prime _ v

/-- Explicit finite-product formula for the total power-residue symbol. -/
theorem fractionalPthPowerResidueSymbol_apply
    (η : NumberField.RingOfIntegers (PrimeCyclotomicField p))
    (I : (FractionalIdeal
      (nonZeroDivisors
        (NumberField.RingOfIntegers (PrimeCyclotomicField p)))
      (PrimeCyclotomicField p))ˣ) :
    fractionalPthPowerResidueSymbol η I =
      (NumberTheory.UnramifiedArtin.fractionalIdealDivisor
        (NumberField.RingOfIntegers (PrimeCyclotomicField p))
        (PrimeCyclotomicField p) (Additive.ofMul I)).prod
        (fun v n => (totalPthPowerResidueSymbolAtPrime η v) ^ n) :=
  NumberTheory.UnramifiedArtin.fractionalIdealHom_apply _ I

/-- Every total residue product has exponent dividing \`p\`. -/
theorem fractionalPthPowerResidueSymbol_pow_eq_one
    (η : NumberField.RingOfIntegers (PrimeCyclotomicField p))
    (I : (FractionalIdeal
      (nonZeroDivisors
        (NumberField.RingOfIntegers (PrimeCyclotomicField p)))
      (PrimeCyclotomicField p))ˣ) :
    (fractionalPthPowerResidueSymbol η I) ^ p = 1 := by
  apply Subtype.ext
  exact (fractionalPthPowerResidueSymbol η I).2

/-- Consequently the total residue product kills every \`p\`-th power of a
nonzero fractional ideal. -/
theorem fractionalPthPowerResidueSymbol_ideal_pow_eq_one
    (η : NumberField.RingOfIntegers (PrimeCyclotomicField p))
    (I : (FractionalIdeal
      (nonZeroDivisors
        (NumberField.RingOfIntegers (PrimeCyclotomicField p)))
      (PrimeCyclotomicField p))ˣ) :
    fractionalPthPowerResidueSymbol η (I ^ p) = 1 := by
  rw [map_pow]
  exact fractionalPthPowerResidueSymbol_pow_eq_one η I

/-- If the principal ideal of \`η\` is a \`p\`-th power, every total residue
product is trivial on \`(η)\`, independently of the numerator used in that
product. -/
theorem fractionalPthPowerResidueSymbol_principal_eq_one_of_span_eq_pow
    (ξ η : NumberField.RingOfIntegers (PrimeCyclotomicField p))
    (hη : η ≠ 0)
    (B : Ideal
      (NumberField.RingOfIntegers (PrimeCyclotomicField p)))
    (hspan : Ideal.span {η} = B ^ p) :
    fractionalPthPowerResidueSymbol ξ
      (toPrincipalIdeal
        (NumberField.RingOfIntegers (PrimeCyclotomicField p))
        (PrimeCyclotomicField p)
        (Units.mk0
          (algebraMap
            (NumberField.RingOfIntegers (PrimeCyclotomicField p))
            (PrimeCyclotomicField p) η)
          ((IsFractionRing.injective
            (NumberField.RingOfIntegers (PrimeCyclotomicField p))
            (PrimeCyclotomicField p)).ne hη))) = 1 := by
  let R := NumberField.RingOfIntegers (PrimeCyclotomicField p)
  let K := PrimeCyclotomicField p
  have hB : B ≠ ⊥ := by
    intro hB
    have hηspan := hspan
    have hbotpow :
        (⊥ : Ideal
          (NumberField.RingOfIntegers (PrimeCyclotomicField p))) ^ p =
            ⊥ := by
      rw [← Ideal.zero_eq_bot, zero_pow (Fact.out : p.Prime).ne_zero]
    rw [hB, hbotpow] at hηspan
    exact hη (Ideal.span_singleton_eq_bot.mp hηspan)
  have hηmap : algebraMap R K η ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective R K).ne hη
  let B₀ : (Ideal R)⁰ :=
    ⟨B, mem_nonZeroDivisors_iff_ne_zero.mpr hB⟩
  let Bu : (FractionalIdeal R⁰ K)ˣ :=
    FractionalIdeal.mk0 K B₀
  have hprincipal :
      toPrincipalIdeal R K
          (Units.mk0 (algebraMap R K η) hηmap) =
        Bu ^ p := by
    apply Units.ext
    simp only [coe_toPrincipalIdeal, Units.val_pow_eq_pow_val,
      FractionalIdeal.coe_mk0, Units.val_mk0, Bu, B₀]
    change FractionalIdeal.spanSingleton R⁰ (algebraMap R K η) =
      ((B : Ideal R) : FractionalIdeal R⁰ K) ^ p
    rw [← FractionalIdeal.coeIdeal_span_singleton, hspan,
      FractionalIdeal.coeIdeal_pow]
  rw [hprincipal]
  exact fractionalPthPowerResidueSymbol_ideal_pow_eq_one ξ Bu

private theorem finitePrime_eq_cyclotomicPrime_of_prime_mem
    (v : FinitePrime (PrimeCyclotomicField p))
    (hpv : (p : NumberField.RingOfIntegers (PrimeCyclotomicField p)) ∈
      v.asIdeal) :
    v = cyclotomicPrime p := by
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  letI : NeZero (p : ℚ) :=
    ⟨Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero⟩
  letI : IsCyclotomicExtension {p} ℚ (PrimeCyclotomicField p) :=
    CyclotomicField.isCyclotomicExtension p ℚ
  letI : v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := by
    rw [Ideal.liesOver_iff]
    have hunder_ne : v.asIdeal.under ℤ ≠ ⊤ := by
      exact Ideal.comap_ne_top
        (algebraMap ℤ
          (NumberField.RingOfIntegers (PrimeCyclotomicField p)))
        v.isPrime.ne_top
    refine Ideal.IsMaximal.eq_of_le
      (Int.ideal_span_isMaximal_of_prime p) hunder_ne ?_
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap,
      algebraMap_int_eq, map_natCast]
    exact hpv
  apply IsDedekindDomain.HeightOneSpectrum.ext
  change v.asIdeal = Ideal.span
    {(IsCyclotomicExtension.zeta_spec p ℚ
      (PrimeCyclotomicField p)).toInteger - 1}
  exact IsCyclotomicExtension.Rat.eq_span_zeta_sub_one_of_liesOver'
    p (PrimeCyclotomicField p)
      (IsCyclotomicExtension.zeta_spec p ℚ (PrimeCyclotomicField p))
      v.asIdeal

omit [Fact p.Prime] in
private theorem mem_of_principal_divisor_ne_zero
    (a : NumberField.RingOfIntegers (PrimeCyclotomicField p))
    (ha : a ≠ 0)
    (v : FinitePrime (PrimeCyclotomicField p))
    (hv :
      NumberTheory.UnramifiedArtin.fractionalIdealDivisor
        (NumberField.RingOfIntegers (PrimeCyclotomicField p))
        (PrimeCyclotomicField p)
        (Additive.ofMul
          (toPrincipalIdeal
            (NumberField.RingOfIntegers (PrimeCyclotomicField p))
            (PrimeCyclotomicField p)
            (Units.mk0
              (algebraMap
                (NumberField.RingOfIntegers (PrimeCyclotomicField p))
                (PrimeCyclotomicField p) a)
              (by
                simpa only [map_zero] using
                  (IsFractionRing.injective
                    (NumberField.RingOfIntegers (PrimeCyclotomicField p))
                    (PrimeCyclotomicField p)).ne ha)))) v ≠ 0) :
    a ∈ v.asIdeal := by
  let R := NumberField.RingOfIntegers (PrimeCyclotomicField p)
  let K := PrimeCyclotomicField p
  have hvcount :
      FractionalIdeal.count K v
        (FractionalIdeal.spanSingleton R⁰ (algebraMap R K a)) ≠ 0 := by
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
    (Associates.count_ne_zero_iff_dvd hspan v.irreducible).mp
      hvcountNat
  exact (Ideal.dvd_span_singleton).mp hvdvd

omit [Fact p.Prime] in
private theorem not_mem_of_coprime_principal_ideals
    (a η : NumberField.RingOfIntegers (PrimeCyclotomicField p))
    (v : FinitePrime (PrimeCyclotomicField p))
    (hcoprime : IsCoprime (Ideal.span {η}) (Ideal.span {a}))
    (hav : a ∈ v.asIdeal) :
    η ∉ v.asIdeal := by
  intro hηv
  apply v.isPrime.ne_top
  apply top_unique
  rw [← hcoprime.sup_eq]
  exact sup_le
    ((Ideal.span_singleton_le_iff_mem v.asIdeal).mpr hηv)
    ((Ideal.span_singleton_le_iff_mem v.asIdeal).mpr hav)

private theorem prime_not_mem_of_mem_coprime_cyclotomic
    (a : NumberField.RingOfIntegers (PrimeCyclotomicField p))
    (v : FinitePrime (PrimeCyclotomicField p))
    (hcoprime :
      IsCoprime (Ideal.span {a}) (cyclotomicPrime p).asIdeal)
    (hav : a ∈ v.asIdeal) :
    (p : NumberField.RingOfIntegers (PrimeCyclotomicField p)) ∉
      v.asIdeal := by
  intro hpv
  have hv : v = cyclotomicPrime p :=
    finitePrime_eq_cyclotomicPrime_of_prime_mem v hpv
  have haCyclotomic : a ∈ (cyclotomicPrime p).asIdeal := by
    rwa [← hv]
  apply (cyclotomicPrime p).isPrime.ne_top
  apply top_unique
  rw [← hcoprime.sup_eq]
  exact sup_le
    ((Ideal.span_singleton_le_iff_mem
      (cyclotomicPrime p).asIdeal).mpr haCyclotomic)
    le_rfl

private theorem isCoprime_cyclotomicPrime_of_not_mem
    (a : NumberField.RingOfIntegers (PrimeCyclotomicField p))
    (ha : a ∉ (cyclotomicPrime p).asIdeal) :
    IsCoprime (Ideal.span {a}) (cyclotomicPrime p).asIdeal := by
  rw [Ideal.isCoprime_iff_codisjoint, codisjoint_comm]
  apply ((cyclotomicPrime p).isMaximal.out.not_le_iff_codisjoint).mp
  intro hle
  exact ha ((Ideal.span_singleton_le_iff_mem
    (cyclotomicPrime p).asIdeal).mp hle)

/-- On an integral principal ideal coprime to both the normalized numerator
and the cyclotomic prime, the Kummer--Frobenius product is the finite
power-residue product with that normalized numerator. -/
theorem KummerPresentation.fractionalKummerSymbol_integralPrincipal_eq_residueProduct
    (E : InverseExtension p L) (P : KummerPresentation E)
    (η a : NumberField.RingOfIntegers (PrimeCyclotomicField p))
    (ha : a ≠ 0)
    (c : (PrimeCyclotomicField p)ˣ)
    (hη : algebraMap
      (NumberField.RingOfIntegers (PrimeCyclotomicField p))
      (PrimeCyclotomicField p) η = P.radicand * (c :
        PrimeCyclotomicField p) ^ p)
    (hcoprimeηa : IsCoprime (Ideal.span {η}) (Ideal.span {a}))
    (hcoprimeaPrime :
      IsCoprime (Ideal.span {a}) (cyclotomicPrime p).asIdeal) :
    P.fractionalKummerSymbol E
        (toPrincipalIdeal
          (NumberField.RingOfIntegers (PrimeCyclotomicField p))
          (PrimeCyclotomicField p)
          (Units.mk0
            (algebraMap
              (NumberField.RingOfIntegers (PrimeCyclotomicField p))
              (PrimeCyclotomicField p) a)
            (by
              simpa only [map_zero] using
                (IsFractionRing.injective
                  (NumberField.RingOfIntegers (PrimeCyclotomicField p))
                  (PrimeCyclotomicField p)).ne ha))) =
      fractionalPthPowerResidueSymbol η
        (toPrincipalIdeal
          (NumberField.RingOfIntegers (PrimeCyclotomicField p))
          (PrimeCyclotomicField p)
          (Units.mk0
            (algebraMap
              (NumberField.RingOfIntegers (PrimeCyclotomicField p))
              (PrimeCyclotomicField p) a)
            (by
              simpa only [map_zero] using
                (IsFractionRing.injective
                  (NumberField.RingOfIntegers (PrimeCyclotomicField p))
                  (PrimeCyclotomicField p)).ne ha))) := by
  classical
  rw [P.fractionalKummerSymbol_apply E,
    fractionalPthPowerResidueSymbol_apply]
  apply Finsupp.prod_congr
  intro v hv
  have hcoefficient := Finsupp.mem_support_iff.mp hv
  have hav : a ∈ v.asIdeal :=
    mem_of_principal_divisor_ne_zero a ha v hcoefficient
  have hηv : η ∉ v.asIdeal :=
    not_mem_of_coprime_principal_ideals a η v hcoprimeηa hav
  have hpv :
      (p : NumberField.RingOfIntegers (PrimeCyclotomicField p)) ∉
        v.asIdeal :=
    prime_not_mem_of_mem_coprime_cyclotomic a v hcoprimeaPrime hav
  have hlocal :
      P.localKummerFrobeniusSymbol E v =
        totalPthPowerResidueSymbolAtPrime η v := by
    rw [P.localKummerFrobeniusSymbol_eq_pairing E,
      totalPthPowerResidueSymbolAtPrime_of_not_mem η v hηv hpv]
    exact P.pairing_frobeniusAt_eq_pthPowerResidueSymbolAtPrime
      E v η c hη hηv hpv
  rw [hlocal]

/-- For normalized data, the integral Kummer product target is equivalent
to equality of the two oppositely oriented finite residue products.  The
reverse product is one because the principal ideal of the normalized
numerator is a `p`-th power; no reciprocity equality is asserted. -/
theorem KummerPresentation.integralProduct_eq_one_iff_twoSidedResidueProduct
    (E : InverseExtension p L) (P : KummerPresentation E)
    (η a : NumberField.RingOfIntegers (PrimeCyclotomicField p))
    (hηne : η ≠ 0) (ha : a ≠ 0)
    (c : (PrimeCyclotomicField p)ˣ)
    (hη : algebraMap
      (NumberField.RingOfIntegers (PrimeCyclotomicField p))
      (PrimeCyclotomicField p) η = P.radicand * (c :
        PrimeCyclotomicField p) ^ p)
    (B : Ideal
      (NumberField.RingOfIntegers (PrimeCyclotomicField p)))
    (hspan : Ideal.span {η} = B ^ p)
    (hcoprimeηa : IsCoprime (Ideal.span {η}) (Ideal.span {a}))
    (hcoprimeaPrime :
      IsCoprime (Ideal.span {a}) (cyclotomicPrime p).asIdeal) :
    (P.fractionalKummerSymbol E
          (toPrincipalIdeal
            (NumberField.RingOfIntegers (PrimeCyclotomicField p))
            (PrimeCyclotomicField p)
            (Units.mk0
              (algebraMap
                (NumberField.RingOfIntegers (PrimeCyclotomicField p))
                (PrimeCyclotomicField p) a)
              (by
                simpa only [map_zero] using
                  (IsFractionRing.injective
                    (NumberField.RingOfIntegers (PrimeCyclotomicField p))
                    (PrimeCyclotomicField p)).ne ha))) = 1) ↔
      fractionalPthPowerResidueSymbol η
          (toPrincipalIdeal
            (NumberField.RingOfIntegers (PrimeCyclotomicField p))
            (PrimeCyclotomicField p)
            (Units.mk0
              (algebraMap
                (NumberField.RingOfIntegers (PrimeCyclotomicField p))
                (PrimeCyclotomicField p) a)
              (by
                simpa only [map_zero] using
                  (IsFractionRing.injective
                    (NumberField.RingOfIntegers (PrimeCyclotomicField p))
                    (PrimeCyclotomicField p)).ne ha))) =
        fractionalPthPowerResidueSymbol a
          (toPrincipalIdeal
            (NumberField.RingOfIntegers (PrimeCyclotomicField p))
            (PrimeCyclotomicField p)
            (Units.mk0
              (algebraMap
                (NumberField.RingOfIntegers (PrimeCyclotomicField p))
                (PrimeCyclotomicField p) η)
              (by
                simpa only [map_zero] using
                  (IsFractionRing.injective
                    (NumberField.RingOfIntegers (PrimeCyclotomicField p))
                    (PrimeCyclotomicField p)).ne hηne))) := by
  rw [P.fractionalKummerSymbol_integralPrincipal_eq_residueProduct
    E η a ha c hη hcoprimeηa hcoprimeaPrime]
  have hreverse :=
    fractionalPthPowerResidueSymbol_principal_eq_one_of_span_eq_pow
      a η hηne B hspan
  rw [hreverse]

/-- A pseudo-unit normalization packages the integral Kummer target as the
remaining two-sided finite residue-product identity.  In particular, this
theorem records a checked reduction, not an assumption or a proof of that
identity. -/
theorem exists_normalization_integralProduct_eq_one_iff_twoSidedResidueProduct
    (E : InverseExtension p L)
    (hdiv : ∀ v : FinitePrime (PrimeCyclotomicField p),
      (p : ℤ) ∣ FractionalIdeal.count (PrimeCyclotomicField p) v
        (FractionalIdeal.spanSingleton
          (nonZeroDivisors
            (NumberField.RingOfIntegers (PrimeCyclotomicField p)))
          E.kummerPresentation.radicand))
    (a : NumberField.RingOfIntegers (PrimeCyclotomicField p))
    (ha : a ≠ 0)
    (haPrime : a ∉ (cyclotomicPrime p).asIdeal) :
    ∃ (c : (PrimeCyclotomicField p)ˣ)
        (η : NumberField.RingOfIntegers (PrimeCyclotomicField p))
        (B : Ideal
          (NumberField.RingOfIntegers (PrimeCyclotomicField p)))
        (hηne : η ≠ 0),
      algebraMap
          (NumberField.RingOfIntegers (PrimeCyclotomicField p))
          (PrimeCyclotomicField p) η =
        E.kummerPresentation.radicand *
          (c : PrimeCyclotomicField p) ^ p ∧
      Ideal.span {η} = B ^ p ∧
      IsCoprime (Ideal.span {η}) (Ideal.span {a}) ∧
      IsCoprime (Ideal.span {η}) (cyclotomicPrime p).asIdeal ∧
      fractionalPthPowerResidueSymbol a
          (toPrincipalIdeal
            (NumberField.RingOfIntegers (PrimeCyclotomicField p))
            (PrimeCyclotomicField p)
            (Units.mk0
              (algebraMap
                (NumberField.RingOfIntegers (PrimeCyclotomicField p))
                (PrimeCyclotomicField p) η)
              (by
                simpa only [map_zero] using
                    (IsFractionRing.injective
                      (NumberField.RingOfIntegers (PrimeCyclotomicField p))
                      (PrimeCyclotomicField p)).ne hηne))) = 1 ∧
      ((E.kummerPresentation.fractionalKummerSymbol E
            (toPrincipalIdeal
              (NumberField.RingOfIntegers (PrimeCyclotomicField p))
              (PrimeCyclotomicField p)
              (Units.mk0
                (algebraMap
                  (NumberField.RingOfIntegers (PrimeCyclotomicField p))
                  (PrimeCyclotomicField p) a)
                (by
                  simpa only [map_zero] using
                    (IsFractionRing.injective
                      (NumberField.RingOfIntegers (PrimeCyclotomicField p))
                      (PrimeCyclotomicField p)).ne ha))) = 1) ↔
        fractionalPthPowerResidueSymbol η
            (toPrincipalIdeal
              (NumberField.RingOfIntegers (PrimeCyclotomicField p))
              (PrimeCyclotomicField p)
              (Units.mk0
                (algebraMap
                  (NumberField.RingOfIntegers (PrimeCyclotomicField p))
                  (PrimeCyclotomicField p) a)
                (by
                  simpa only [map_zero] using
                    (IsFractionRing.injective
                      (NumberField.RingOfIntegers (PrimeCyclotomicField p))
                      (PrimeCyclotomicField p)).ne ha))) =
          fractionalPthPowerResidueSymbol a
            (toPrincipalIdeal
              (NumberField.RingOfIntegers (PrimeCyclotomicField p))
              (PrimeCyclotomicField p)
              (Units.mk0
                (algebraMap
                  (NumberField.RingOfIntegers (PrimeCyclotomicField p))
                  (PrimeCyclotomicField p) η)
                (by
                  simpa only [map_zero] using
                    (IsFractionRing.injective
                      (NumberField.RingOfIntegers (PrimeCyclotomicField p))
                      (PrimeCyclotomicField p)).ne hηne)))) := by
  have hspan_a : Ideal.span {a} ≠ ⊥ :=
    Ideal.span_singleton_eq_bot.not.mpr ha
  obtain ⟨c, η, B, hηne, hη, hspan, hcoprimeηa,
      hcoprimeηPrime⟩ :=
    E.exists_coprime_integral_pseudoUnit_normalization
      hdiv (Ideal.span {a}) hspan_a
  refine ⟨c, η, B, hηne, hη, hspan, hcoprimeηa,
    hcoprimeηPrime, ?_, ?_⟩
  · exact fractionalPthPowerResidueSymbol_principal_eq_one_of_span_eq_pow
      a η hηne B hspan
  · exact E.kummerPresentation.integralProduct_eq_one_iff_twoSidedResidueProduct
      E η a hηne ha c hη B hspan hcoprimeηa
        (isCoprime_cyclotomicPrime_of_not_mem a haPrime)

end NumberTheory.CyclotomicCharacter.InverseExtension
