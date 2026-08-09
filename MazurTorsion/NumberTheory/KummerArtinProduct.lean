/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.CyclotomicNormalizedLocalPrimary

/-!
# Kummer coordinates for the finite-prime Artin product

This file rewrites the ideal-theoretic Artin map of an inverse-cyclotomic
extension in the Kummer pairing attached to a chosen radical.  The resulting
principal product formula is proved equivalent, without an arithmetic
assumption, to conductor-one principal reciprocity for the original Artin
map.  The genuinely global assertion is then isolated as a named principle.
-/

open scoped NumberField nonZeroDivisors

namespace NumberTheory.CyclotomicCharacter.InverseExtension

universe u

variable {p : ℕ} [Fact p.Prime]
variable {L : Type u} [Field L] [NumberField L]
variable [Algebra (PrimeCyclotomicField p) L]
variable [IsScalarTower ℚ (PrimeCyclotomicField p) L]

/-- The exact principal product formula in Kummer coordinates: the finite
product of local Kummer/Frobenius symbols attached to every principal
fractional ideal is one. -/
def KummerPresentation.SatisfiesPrincipalProductFormula
    (E : InverseExtension p L) (P : KummerPresentation E) : Prop :=
  ∀ x : (PrimeCyclotomicField p)ˣ,
    (NumberTheory.UnramifiedArtin.fractionalIdealDivisor
      (NumberField.RingOfIntegers (PrimeCyclotomicField p))
      (PrimeCyclotomicField p)
      (Additive.ofMul
        (toPrincipalIdeal
          (NumberField.RingOfIntegers (PrimeCyclotomicField p))
          (PrimeCyclotomicField p) x))).prod
      (fun v n => (P.localKummerFrobeniusSymbol E v) ^ n) = 1

/-- The explicit product formula is the statement that the fractional
Kummer-symbol homomorphism kills principal ideals. -/
theorem KummerPresentation.satisfiesPrincipalProductFormula_iff_kills
    (E : InverseExtension p L) (P : KummerPresentation E) :
    P.SatisfiesPrincipalProductFormula E ↔
      NumberTheory.UnramifiedArtin.KillsPrincipalIdeals
        (NumberField.RingOfIntegers (PrimeCyclotomicField p))
        (PrimeCyclotomicField p) (P.fractionalKummerSymbol E) := by
  constructor
  · intro h x
    rw [P.fractionalKummerSymbol_apply E]
    exact h x
  · intro h x
    rw [← P.fractionalKummerSymbol_apply E]
    exact h x

/-- Changing from cyclic coordinates to Kummer coordinates preserves and
reflects the property of killing all principal fractional ideals. -/
theorem KummerPresentation.killsPrincipalKummerSymbols_iff_reciprocity
    (E : InverseExtension p L) (P : KummerPresentation E) :
    NumberTheory.UnramifiedArtin.KillsPrincipalIdeals
        (NumberField.RingOfIntegers (PrimeCyclotomicField p))
        (PrimeCyclotomicField p) (P.fractionalKummerSymbol E) ↔
      E.SatisfiesPrincipalReciprocity := by
  rw [P.fractionalKummerSymbol_eq_coordinate_comp E]
  constructor
  · intro h x
    apply (P.coordinateEquiv E).injective
    change P.coordinateEquiv E
        (E.fractionalArtin
          (toPrincipalIdeal
            (NumberField.RingOfIntegers (PrimeCyclotomicField p))
            (PrimeCyclotomicField p) x)) =
      P.coordinateEquiv E 1
    simpa using h x
  · intro h x
    change P.coordinateEquiv E
        (E.fractionalArtin
          (toPrincipalIdeal
            (NumberField.RingOfIntegers (PrimeCyclotomicField p))
            (PrimeCyclotomicField p) x)) = 1
    rw [h x, map_one]

/-- The Kummer principal product formula is an exact reformulation of
conductor-one principal reciprocity for the ideal Artin map. -/
theorem KummerPresentation.satisfiesPrincipalProductFormula_iff_reciprocity
    (E : InverseExtension p L) (P : KummerPresentation E) :
    P.SatisfiesPrincipalProductFormula E ↔
      E.SatisfiesPrincipalReciprocity :=
  (P.satisfiesPrincipalProductFormula_iff_kills E).trans
    (P.killsPrincipalKummerSymbols_iff_reciprocity E)

/-- The explicit Kummer product formula holds on principal ideals generated
by rational units.  Thus the integer-denominator part of cyclotomic
reciprocity is already forced by inverse-character equivariance; the missing
arithmetic input concerns genuinely cyclotomic generators. -/
theorem KummerPresentation.rationalPrincipalProductFormula
    (hp : 2 < p)
    (E : InverseExtension p L) (P : KummerPresentation E)
    (hunramified : E.IsUnramifiedAtFinitePlaces)
    (a : ℚˣ) :
    (NumberTheory.UnramifiedArtin.fractionalIdealDivisor
      (NumberField.RingOfIntegers (PrimeCyclotomicField p))
      (PrimeCyclotomicField p)
      (Additive.ofMul
        (toPrincipalIdeal
          (NumberField.RingOfIntegers (PrimeCyclotomicField p))
          (PrimeCyclotomicField p)
          (Units.map
            (algebraMap ℚ (PrimeCyclotomicField p)).toMonoidHom a)))).prod
      (fun v n => (P.localKummerFrobeniusSymbol E v) ^ n) = 1 := by
  rw [← P.fractionalKummerSymbol_apply E]
  rw [P.fractionalKummerSymbol_eq_coordinate_comp E]
  change P.coordinateEquiv E
      (E.fractionalArtin
        (toPrincipalIdeal
          (NumberField.RingOfIntegers (PrimeCyclotomicField p))
          (PrimeCyclotomicField p)
          (Units.map
            (algebraMap ℚ (PrimeCyclotomicField p)).toMonoidHom a))) = 1
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  letI : NeZero (p : ℚ) :=
    ⟨Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero⟩
  letI : IsCyclotomicExtension {p} ℚ (PrimeCyclotomicField p) :=
    CyclotomicField.isCyclotomicExtension p ℚ
  letI : Fact (2 < p) := ⟨hp⟩
  let e : Gal(PrimeCyclotomicField p/ℚ) ≃* (ZMod p)ˣ :=
    IsCyclotomicExtension.autEquivPow (PrimeCyclotomicField p)
      (Polynomial.cyclotomic.irreducible_rat (NeZero.pos p))
  let sigma : Gal(PrimeCyclotomicField p/ℚ) := e.symm (-1)
  have hcharacter : inverseCharacter p sigma = (-1 : (ZMod p)ˣ) := by
    change (e sigma)⁻¹ = -1
    rw [e.apply_symm_apply]
    simp
  have hsigma : (inverseCharacter p sigma : ZMod p) ≠ 1 := by
    rw [hcharacter]
    exact ZMod.neg_one_ne_one
  have hfixed :
      sigma
          ((Units.map
            (algebraMap ℚ (PrimeCyclotomicField p)).toMonoidHom a :
              (PrimeCyclotomicField p)ˣ) : PrimeCyclotomicField p) =
        ((Units.map
            (algebraMap ℚ (PrimeCyclotomicField p)).toMonoidHom a :
              (PrimeCyclotomicField p)ˣ) : PrimeCyclotomicField p) := by
    change sigma (algebraMap ℚ (PrimeCyclotomicField p) (a : ℚ)) =
      algebraMap ℚ (PrimeCyclotomicField p) (a : ℚ)
    exact sigma.commutes (a : ℚ)
  rw [E.fractionalArtin_toPrincipalIdeal_eq_one_of_fixed
    hunramified sigma hsigma _ hfixed]
  exact map_one (P.coordinateEquiv E)

/-- Principal reciprocity away from the unique cyclotomic prime.  The count
condition says exactly that the principal fractional ideal has no factor at
the prime generated by `ζ_p - 1`. -/
def SatisfiesPrimeToCyclotomicPrincipalReciprocity
    (E : InverseExtension p L) : Prop :=
  ∀ x : (PrimeCyclotomicField p)ˣ,
    FractionalIdeal.count (PrimeCyclotomicField p) (cyclotomicPrime p)
        (toPrincipalIdeal
          (NumberField.RingOfIntegers (PrimeCyclotomicField p))
          (PrimeCyclotomicField p) x :
          FractionalIdeal
            (nonZeroDivisors
              (NumberField.RingOfIntegers (PrimeCyclotomicField p)))
            (PrimeCyclotomicField p)) = 0 →
      E.fractionalArtin
        (toPrincipalIdeal
          (NumberField.RingOfIntegers (PrimeCyclotomicField p))
          (PrimeCyclotomicField p) x) = 1

/-- Integral principal reciprocity away from the cyclotomic prime.  The
checked denominator-clearing theorem below shows that this integral
condition already controls every prime-to-cyclotomic field unit. -/
def SatisfiesIntegralPrimeToCyclotomicPrincipalReciprocity
    (E : InverseExtension p L) : Prop :=
  ∀ (a : NumberField.RingOfIntegers (PrimeCyclotomicField p)) (ha : a ≠ 0),
    a ∉ (cyclotomicPrime p).asIdeal →
    E.fractionalArtin
      (toPrincipalIdeal
        (NumberField.RingOfIntegers (PrimeCyclotomicField p))
        (PrimeCyclotomicField p)
        (Units.mk0
          (algebraMap
            (NumberField.RingOfIntegers (PrimeCyclotomicField p))
            (PrimeCyclotomicField p) a)
          ((IsFractionRing.injective
            (NumberField.RingOfIntegers (PrimeCyclotomicField p))
            (PrimeCyclotomicField p)).ne ha))) = 1

/-- Integral prime-to-cyclotomic principal reciprocity in the canonical
Kummer/Frobenius coordinate. -/
def KummerPresentation.SatisfiesIntegralPrimeToCyclotomicProductFormula
    (E : InverseExtension p L) (P : KummerPresentation E) : Prop :=
  ∀ (a : NumberField.RingOfIntegers (PrimeCyclotomicField p)) (ha : a ≠ 0),
    a ∉ (cyclotomicPrime p).asIdeal →
    P.fractionalKummerSymbol E
      (toPrincipalIdeal
        (NumberField.RingOfIntegers (PrimeCyclotomicField p))
        (PrimeCyclotomicField p)
        (Units.mk0
          (algebraMap
            (NumberField.RingOfIntegers (PrimeCyclotomicField p))
            (PrimeCyclotomicField p) a)
          ((IsFractionRing.injective
            (NumberField.RingOfIntegers (PrimeCyclotomicField p))
            (PrimeCyclotomicField p)).ne ha))) = 1

/-- The integral Kummer product formula is exactly integral Artin
reciprocity after the already-checked change of cyclic coordinate. -/
theorem KummerPresentation.satisfiesIntegralPrimeToCyclotomicProductFormula_iff
    (E : InverseExtension p L) (P : KummerPresentation E) :
    P.SatisfiesIntegralPrimeToCyclotomicProductFormula E ↔
      E.SatisfiesIntegralPrimeToCyclotomicPrincipalReciprocity := by
  constructor
  · intro h a ha hprime
    have hs := h a ha hprime
    rw [P.fractionalKummerSymbol_eq_coordinate_comp E] at hs
    apply (P.coordinateEquiv E).injective
    simpa using hs
  · intro h a ha hprime
    rw [P.fractionalKummerSymbol_eq_coordinate_comp E]
    change P.coordinateEquiv E
        (E.fractionalArtin
          (toPrincipalIdeal
            (NumberField.RingOfIntegers (PrimeCyclotomicField p))
            (PrimeCyclotomicField p)
            (Units.mk0
              (algebraMap
                (NumberField.RingOfIntegers (PrimeCyclotomicField p))
                (PrimeCyclotomicField p) a)
              ((IsFractionRing.injective
                (NumberField.RingOfIntegers (PrimeCyclotomicField p))
                (PrimeCyclotomicField p)).ne ha)))) = 1
    rw [h a ha hprime, map_one]

/-- The pseudo-unit divisor condition on a Kummer radicand: every finite
prime exponent of its principal fractional ideal is divisible by `p`. -/
def KummerPresentation.HasPDivisibleFiniteDivisor
    (E : InverseExtension p L) (P : KummerPresentation E) : Prop :=
  ∀ v : FinitePrime (PrimeCyclotomicField p),
    (p : ℤ) ∣ FractionalIdeal.count (PrimeCyclotomicField p) v
      (FractionalIdeal.spanSingleton
        (nonZeroDivisors
          (NumberField.RingOfIntegers (PrimeCyclotomicField p)))
        P.radicand)

/-- The pseudo-unit divisor hypothesis already kills the principal ideal of
the radicand itself under the canonical Kummer symbol.  One-sided
reciprocity is the additional assertion for an arbitrary principal
denominator. -/
theorem KummerPresentation.fractionalKummerSymbol_principalRadicand_eq_one
    (E : InverseExtension p L)
    (hdiv : E.kummerPresentation.HasPDivisibleFiniteDivisor E) :
    E.kummerPresentation.fractionalKummerSymbol E
      (toPrincipalIdeal
        (NumberField.RingOfIntegers (PrimeCyclotomicField p))
        (PrimeCyclotomicField p)
        (Units.mk0 E.kummerPresentation.radicand
          (E.kummerPresentation.radicand_ne_zero E))) = 1 := by
  exact E.rawKummerSymbol_principalRadicand_eq_one_of_dvd_counts hdiv

/-- The local-primary condition used by one-sided Kummer reciprocity: the
radicand is a `p`-th power in the cyclotomic-prime completion. -/
def KummerPresentation.IsPthPowerAtCyclotomicPrime
    (E : InverseExtension p L) (P : KummerPresentation E) : Prop :=
  ∃ y : (cyclotomicPrime p).adicCompletion (PrimeCyclotomicField p),
    y ^ p = algebraMap (PrimeCyclotomicField p)
      ((cyclotomicPrime p).adicCompletion (PrimeCyclotomicField p)) P.radicand

/-- A normalized integral numerator produced from a locally primary Kummer
radicand is finite-primary whenever the normalization is coprime to the
cyclotomic prime.  This is the form in which the local congruence enters the
one-sided reciprocity argument. -/
theorem KummerPresentation.isFinitePrimaryAtCyclotomicPrime_of_normalization_coprime
    (E : InverseExtension p L) (P : KummerPresentation E)
    (hlocal : P.IsPthPowerAtCyclotomicPrime E)
    (η : NumberField.RingOfIntegers (PrimeCyclotomicField p))
    (c : (PrimeCyclotomicField p)ˣ)
    (hη : algebraMap
      (NumberField.RingOfIntegers (PrimeCyclotomicField p))
      (PrimeCyclotomicField p) η =
        P.radicand * (c : PrimeCyclotomicField p) ^ p)
    (hcoprimeηPrime :
      IsCoprime (Ideal.span {η}) (cyclotomicPrime p).asIdeal) :
    IsFinitePrimaryAtCyclotomicPrime η := by
  apply P.isFinitePrimaryAtCyclotomicPrime_of_localRoot_normalization
    E hlocal η c hη
  intro hηPrime
  apply (cyclotomicPrime p).isPrime.ne_top
  apply top_unique
  rw [← hcoprimeηPrime.sup_eq]
  exact sup_le
    ((Ideal.span_singleton_le_iff_mem
      (cyclotomicPrime p).asIdeal).mpr hηPrime)
    le_rfl

/-- Mathlib's prime-complement denominator theorem clears a
prime-to-cyclotomic fractional generator using integral numerator and
denominator that both avoid the cyclotomic prime. -/
theorem satisfiesPrimeToCyclotomicPrincipalReciprocity_of_integral
    (E : InverseExtension p L)
    (hintegral : E.SatisfiesIntegralPrimeToCyclotomicPrincipalReciprocity) :
    E.SatisfiesPrimeToCyclotomicPrincipalReciprocity := by
  intro x hxcount
  let R := NumberField.RingOfIntegers (PrimeCyclotomicField p)
  let K := PrimeCyclotomicField p
  let v := cyclotomicPrime p
  have hxcount' :
      FractionalIdeal.count K v
        (FractionalIdeal.spanSingleton R⁰ (x : K)) = 0 := by
    simpa only [coe_toPrincipalIdeal] using hxcount
  have hcountval := count_spanSingleton_eq_neg_valuationLog
    (p := p) (x : K) x.ne_zero v
  have hxlog : WithZero.log (v.valuation K (x : K)) = 0 := by
    rw [hxcount'] at hcountval
    exact neg_eq_zero.mp hcountval.symm
  have hxval_ne : v.valuation K (x : K) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 x.ne_zero
  have hxval : v.valuation K (x : K) = 1 := by
    rw [← WithZero.exp_log hxval_ne, hxlog, WithZero.exp_zero]
  obtain ⟨n, d, hnd⟩ :=
    v.exists_primeCompl_mul_eq_of_integer (K := K) (x : K) hxval.le
  have hdval : v.valuation K (algebraMap R K (d : R)) = 1 :=
    v.valuation_eq_one_iff_notMem.mpr d.prop
  have hnval : v.valuation K (algebraMap R K n) = 1 := by
    rw [← hnd, map_mul, hxval, hdval, mul_one]
  have hnmem : n ∉ v.asIdeal :=
    v.valuation_eq_one_iff_notMem.mp hnval
  have hnzero : n ≠ 0 := fun hn => hnmem (hn ▸ v.asIdeal.zero_mem)
  have hdzero : (d : R) ≠ 0 := fun hd => d.prop (hd ▸ v.asIdeal.zero_mem)
  let nu : Kˣ := Units.mk0 (algebraMap R K n)
    ((IsFractionRing.injective R K).ne hnzero)
  let du : Kˣ := Units.mk0 (algebraMap R K (d : R))
    ((IsFractionRing.injective R K).ne hdzero)
  have hxu : x * du = nu := by
    apply Units.ext
    exact hnd
  have hnartin := hintegral n hnzero hnmem
  have hdartin := hintegral (d : R) hdzero d.prop
  have hxunits : x = nu / du := by
    rw [← hxu]
    simp
  rw [hxunits, map_div, map_div, hnartin, hdartin, div_one]

/-- Since the cyclotomic prime itself has trivial Artin symbol, reciprocity
for principal ideals prime to that prime already implies reciprocity for all
principal fractional ideals. -/
theorem satisfiesPrincipalReciprocity_of_primeToCyclotomic
    (hp : 2 < p)
    (E : InverseExtension p L)
    (hunramified : E.IsUnramifiedAtFinitePlaces)
    (haway : E.SatisfiesPrimeToCyclotomicPrincipalReciprocity) :
    E.SatisfiesPrincipalReciprocity := by
  intro x
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  letI : NeZero (p : ℚ) :=
    ⟨Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero⟩
  letI : IsCyclotomicExtension {p} ℚ (PrimeCyclotomicField p) :=
    CyclotomicField.isCyclotomicExtension p ℚ
  let zeta := IsCyclotomicExtension.zeta_spec p ℚ (PrimeCyclotomicField p)
  let uniformizerInteger :
      NumberField.RingOfIntegers (PrimeCyclotomicField p) :=
    zeta.toInteger - 1
  have huniformizerInteger : uniformizerInteger ≠ 0 :=
    Prime.ne_zero zeta.zeta_sub_one_prime'
  let uniformizer : (PrimeCyclotomicField p)ˣ :=
    Units.mk0
      (algebraMap
        (NumberField.RingOfIntegers (PrimeCyclotomicField p))
        (PrimeCyclotomicField p) uniformizerInteger)
      ((IsFractionRing.injective
        (NumberField.RingOfIntegers (PrimeCyclotomicField p))
        (PrimeCyclotomicField p)).ne huniformizerInteger)
  have huniformizerIdeal :
      toPrincipalIdeal
          (NumberField.RingOfIntegers (PrimeCyclotomicField p))
          (PrimeCyclotomicField p) uniformizer =
        NumberTheory.UnramifiedArtin.primeFractionalIdealUnit
          (K := PrimeCyclotomicField p) (cyclotomicPrime p) := by
    apply Units.ext
    rw [coe_toPrincipalIdeal]
    change FractionalIdeal.spanSingleton
        (nonZeroDivisors
          (NumberField.RingOfIntegers (PrimeCyclotomicField p)))
        (algebraMap
          (NumberField.RingOfIntegers (PrimeCyclotomicField p))
          (PrimeCyclotomicField p) uniformizerInteger) =
      ((cyclotomicPrime p).asIdeal : FractionalIdeal
        (nonZeroDivisors
          (NumberField.RingOfIntegers (PrimeCyclotomicField p)))
        (PrimeCyclotomicField p))
    rw [← FractionalIdeal.coeIdeal_span_singleton]
    rfl
  let n : ℤ := FractionalIdeal.count (PrimeCyclotomicField p)
    (cyclotomicPrime p)
    (toPrincipalIdeal
      (NumberField.RingOfIntegers (PrimeCyclotomicField p))
      (PrimeCyclotomicField p) x :
      FractionalIdeal
        (nonZeroDivisors
          (NumberField.RingOfIntegers (PrimeCyclotomicField p)))
        (PrimeCyclotomicField p))
  let xAway : (PrimeCyclotomicField p)ˣ := x / uniformizer ^ n
  have hxAwayCount :
      FractionalIdeal.count (PrimeCyclotomicField p) (cyclotomicPrime p)
          (toPrincipalIdeal
            (NumberField.RingOfIntegers (PrimeCyclotomicField p))
            (PrimeCyclotomicField p) xAway :
            FractionalIdeal
              (nonZeroDivisors
                (NumberField.RingOfIntegers (PrimeCyclotomicField p)))
              (PrimeCyclotomicField p)) = 0 := by
    rw [show toPrincipalIdeal
        (NumberField.RingOfIntegers (PrimeCyclotomicField p))
        (PrimeCyclotomicField p) xAway =
      toPrincipalIdeal
          (NumberField.RingOfIntegers (PrimeCyclotomicField p))
          (PrimeCyclotomicField p) x /
        (toPrincipalIdeal
          (NumberField.RingOfIntegers (PrimeCyclotomicField p))
          (PrimeCyclotomicField p) uniformizer) ^ n by
      simp [xAway]]
    rw [Units.val_div_eq_div_val, Units.val_zpow_eq_zpow_val, div_eq_mul_inv]
    rw [FractionalIdeal.count_mul _ _
        (Units.ne_zero _)
        (inv_ne_zero (zpow_ne_zero _ (Units.ne_zero _))),
      FractionalIdeal.count_inv, ← Units.val_zpow_eq_zpow_val, huniformizerIdeal,
      Units.val_zpow_eq_zpow_val,
      NumberTheory.UnramifiedArtin.primeFractionalIdealUnit,
      Units.val_mk0, FractionalIdeal.count_zpow_self]
    change n + -n = 0
    exact add_neg_cancel n
  have hxAway := haway xAway hxAwayCount
  have hprime : E.fractionalArtin
      (NumberTheory.UnramifiedArtin.primeFractionalIdealUnit
        (K := PrimeCyclotomicField p) (cyclotomicPrime p)) = 1 := by
    unfold NumberTheory.UnramifiedArtin.primeFractionalIdealUnit
    rw [E.fractionalArtin_prime]
    exact E.artinSymbol_cyclotomicPrime_eq_one hp hunramified
  have hxdecomp : x = uniformizer ^ n * xAway := by
    simp [xAway]
  rw [hxdecomp, map_mul, map_zpow, huniformizerIdeal, map_mul, map_zpow,
    hprime, one_zpow, one_mul, hxAway]

end NumberTheory.CyclotomicCharacter.InverseExtension

namespace NumberTheory.CyclotomicCharacter

universe u

/-- The exact prime-to-`p` reciprocity input left after removing the unique
cyclotomic-prime factor from every principal fractional ideal. -/
def PrimeToCyclotomicPrincipalReciprocityPrinciple
    (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ {L : Type u} [Field L] [NumberField L]
    [Algebra (PrimeCyclotomicField p) L]
    [IsScalarTower ℚ (PrimeCyclotomicField p) L]
    (E : InverseExtension p L),
    E.IsUnramifiedAtFinitePlaces →
      E.SatisfiesPrimeToCyclotomicPrincipalReciprocity

/-- The exact one-sided Kummer reciprocity kernel after separating all
checked local and normalization inputs.  It assumes only the pseudo-unit
divisor condition and local `p`-th-power condition for the canonical
radicand, and asks for integral principal Kummer-symbol vanishing away from
the cyclotomic prime. -/
def LocallyPrimaryPseudoUnitKummerReciprocityPrinciple
    (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ {L : Type u} [Field L] [NumberField L]
    [Algebra (PrimeCyclotomicField p) L]
    [IsScalarTower ℚ (PrimeCyclotomicField p) L]
    (E : InverseExtension p L),
    E.kummerPresentation.HasPDivisibleFiniteDivisor E →
    E.kummerPresentation.IsPthPowerAtCyclotomicPrime E →
    E.kummerPresentation.SatisfiesIntegralPrimeToCyclotomicProductFormula E

/-- One-sided Kummer reciprocity for locally-primary pseudo-units supplies
prime-to-cyclotomic principal Artin reciprocity.  The Kummer/Frobenius
comparison, both arithmetic hypotheses, and fractional denominator clearing
in this reduction are checked. -/
theorem primeToCyclotomicPrincipalReciprocityPrinciple_of_locallyPrimaryPseudoUnit
    {p : ℕ} [Fact p.Prime] (hp : 2 < p)
    (hreciprocity : LocallyPrimaryPseudoUnitKummerReciprocityPrinciple.{u} p) :
    PrimeToCyclotomicPrincipalReciprocityPrinciple.{u} p := by
  intro L _ _ _ _ E hunramified
  have hpseudo : E.kummerPresentation.HasPDivisibleFiniteDivisor E := by
    intro v
    exact E.prime_dvd_count_unramifiedRadicand hunramified v
  have hlocal : E.kummerPresentation.IsPthPowerAtCyclotomicPrime E :=
    E.cyclotomicPrime_radicand_isPow hp hunramified
  have hkummer := hreciprocity E hpseudo hlocal
  have hintegral :
      E.SatisfiesIntegralPrimeToCyclotomicPrincipalReciprocity :=
    (E.kummerPresentation.satisfiesIntegralPrimeToCyclotomicProductFormula_iff E).mp
      hkummer
  exact E.satisfiesPrimeToCyclotomicPrincipalReciprocity_of_integral hintegral

/-- The missing global product formula, stated in the canonical Kummer
presentation of every everywhere-finite-unramified inverse extension. -/
def KummerArtinProductFormulaPrinciple
    (p : ℕ) [Fact p.Prime] : Prop :=
  NumberField.IsTotallyComplex (PrimeCyclotomicField p) →
    ∀ {L : Type u} [Field L] [NumberField L]
      [Algebra (PrimeCyclotomicField p) L]
      [IsScalarTower ℚ (PrimeCyclotomicField p) L]
      (E : InverseExtension p L),
      E.IsUnramifiedAtFinitePlaces →
        E.kummerPresentation.SatisfiesPrincipalProductFormula E

/-- Prime-to-cyclotomic principal reciprocity implies the full Kummer product
formula. The omitted cyclotomic-prime factor contributes trivially because
its Artin symbol is one. -/
theorem kummerArtinProductFormulaPrinciple_of_primeToCyclotomic
    {p : ℕ} [Fact p.Prime] (hp : 2 < p)
    (haway : PrimeToCyclotomicPrincipalReciprocityPrinciple.{u} p) :
    KummerArtinProductFormulaPrinciple.{u} p := by
  intro _ L _ _ _ _ E hunramified
  exact (E.kummerPresentation.satisfiesPrincipalProductFormula_iff_reciprocity E).mpr
    (E.satisfiesPrincipalReciprocity_of_primeToCyclotomic hp hunramified
      (haway E hunramified))

/-- The global Kummer product formula supplies conductor-one principal
reciprocity for every relevant inverse extension. -/
theorem principalReciprocityPrinciple_of_kummerArtinProductFormula
    {p : ℕ} [Fact p.Prime]
    (hproduct : KummerArtinProductFormulaPrinciple.{u} p) :
    PrincipalReciprocityPrinciple.{u} p := by
  intro hcomplex L _ _ _ _ E hunramified
  exact (E.kummerPresentation.satisfiesPrincipalProductFormula_iff_reciprocity E).mp
      (hproduct hcomplex E hunramified)

/-- Consequently, the global Kummer product formula gives the class-group
quotient required by the cyclotomic obstruction. -/
theorem classFieldTheoryPrinciple_of_kummerArtinProductFormula
    {p : ℕ} [Fact p.Prime]
    (hproduct : KummerArtinProductFormulaPrinciple.{u} p) :
    ClassFieldTheoryPrinciple.{u} p :=
  classFieldTheoryPrinciple_of_principalReciprocity
    (principalReciprocityPrinciple_of_kummerArtinProductFormula hproduct)

end NumberTheory.CyclotomicCharacter
